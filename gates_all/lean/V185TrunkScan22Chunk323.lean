import V185TrunkScan22Chunk322

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2883030 : List Nat := [5, 2, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2883030 : Nat := 118140960795 + 2883030 * 2 ^ 59
def prefixEnd_2883030 : Nat := 4983230072969 + 3 ^ 40 * 2883030 * 2
def baseEnd_2883030 : Nat := 328973362518213414570265

theorem tailTrace_2883030 : CollatzResearch.WordTrace tailWord_2883030 prefixEnd_2883030 328973362518213414570265 := by
  unfold tailWord_2883030
  simp only [CollatzResearch.WordTrace]
  refine ⟨6572046421580135448034409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70101828496854778112367029 6572046421580135448034409)
  ·
    refine ⟨4929034816185101586025807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6572046421580135448034409 4929034816185101586025807)
    ·
      refine ⟨7393552224277652379038711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4929034816185101586025807 7393552224277652379038711)
      ·
        refine ⟨11090328336416478568558067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7393552224277652379038711 11090328336416478568558067)
        ·
          refine ⟨16635492504624717852837101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11090328336416478568558067 16635492504624717852837101)
          ·
            refine ⟨6238309689234269194813913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16635492504624717852837101 6238309689234269194813913)
            ·
              refine ⟨4678732266925701896110435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6238309689234269194813913 4678732266925701896110435)
              ·
                refine ⟨7018098400388552844165653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678732266925701896110435 7018098400388552844165653)
                ·
                  refine ⟨328973362518213414570265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7018098400388552844165653 328973362518213414570265)
                  ·
                    rfl

theorem cell22_2883030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2883030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883030 prefixEnd_2883030 := by exact prefixLift 2883030
  have htrace : WordTrace (prefixWord ++ tailWord_2883030) baseStart_2883030 baseEnd_2883030 := by
    simpa [prefixWord, tailWord_2883030, baseEnd_2883030] using wordTrace_append hprefix tailTrace_2883030
  have hstable : (prefixWord ++ tailWord_2883030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883030).length < 2 ^ (prefixWord ++ tailWord_2883030).sum := by decide
  have hdescent : baseEnd_2883030 < baseStart_2883030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883045 : List Nat := [1, 3, 1, 5, 1, 3, 1, 1, 1, 5]
def baseStart_2883045 : Nat := 118140960795 + 2883045 * 2 ^ 59
def prefixEnd_2883045 : Nat := 4983230072969 + 3 ^ 40 * 2883045 * 2
def baseEnd_2883045 : Nat := 986925222361185204585749

theorem tailTrace_2883045 : CollatzResearch.WordTrace tailWord_2883045 prefixEnd_2883045 986925222361185204585749 := by
  unfold tailWord_2883045
  simp only [CollatzResearch.WordTrace]
  refine ⟨105153289840227824730346589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70102193226818549820231059 105153289840227824730346589)
  ·
    refine ⟨39432483690085434273879971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105153289840227824730346589 39432483690085434273879971)
    ·
      refine ⟨59148725535128151410819957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39432483690085434273879971 59148725535128151410819957)
      ·
        refine ⟨5545193018918264194764371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59148725535128151410819957 5545193018918264194764371)
        ·
          refine ⟨8317789528377396292146557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5545193018918264194764371 8317789528377396292146557)
          ·
            refine ⟨3119171073141523609554959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8317789528377396292146557 3119171073141523609554959)
            ·
              refine ⟨4678756609712285414332439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119171073141523609554959 4678756609712285414332439)
              ·
                refine ⟨7018134914568428121498659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4678756609712285414332439 7018134914568428121498659)
                ·
                  refine ⟨10527202371852642182247989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7018134914568428121498659 10527202371852642182247989)
                  ·
                    refine ⟨986925222361185204585749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10527202371852642182247989 986925222361185204585749)
                    ·
                      rfl

theorem cell22_2883045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 3, 1, 1, 1, 5].length) (baseStart_2883045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883045 prefixEnd_2883045 := by exact prefixLift 2883045
  have htrace : WordTrace (prefixWord ++ tailWord_2883045) baseStart_2883045 baseEnd_2883045 := by
    simpa [prefixWord, tailWord_2883045, baseEnd_2883045] using wordTrace_append hprefix tailTrace_2883045
  have hstable : (prefixWord ++ tailWord_2883045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883045).length < 2 ^ (prefixWord ++ tailWord_2883045).sum := by decide
  have hdescent : baseEnd_2883045 < baseStart_2883045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883058 : List Nat := [3, 2, 1, 4, 1, 2, 1, 8]
def baseStart_2883058 : Nat := 118140960795 + 2883058 * 2 ^ 59
def prefixEnd_2883058 : Nat := 4983230072969 + 3 ^ 40 * 2883058 * 2
def baseEnd_2883058 : Nat := 109658852502984167112301

theorem tailTrace_2883058 : CollatzResearch.WordTrace tailWord_2883058 prefixEnd_2883058 109658852502984167112301 := by
  unfold tailWord_2883058
  simp only [CollatzResearch.WordTrace]
  refine ⟨26288440997295181987642457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70102509326120485300379885 26288440997295181987642457)
  ·
    refine ⟨19716330747971386490731843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26288440997295181987642457 19716330747971386490731843)
    ·
      refine ⟨29574496121957079736097765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19716330747971386490731843 29574496121957079736097765)
      ·
        refine ⟨5545218022866952450518331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29574496121957079736097765 5545218022866952450518331)
        ·
          refine ⟨8317827034300428675777497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5545218022866952450518331 8317827034300428675777497)
          ·
            refine ⟨6238370275725321506833123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8317827034300428675777497 6238370275725321506833123)
            ·
              refine ⟨9357555413587982260249685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6238370275725321506833123 9357555413587982260249685)
              ·
                refine ⟨109658852502984167112301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9357555413587982260249685 109658852502984167112301)
                ·
                  rfl

theorem cell22_2883058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 8].length) (baseStart_2883058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883058 prefixEnd_2883058 := by exact prefixLift 2883058
  have htrace : WordTrace (prefixWord ++ tailWord_2883058) baseStart_2883058 baseEnd_2883058 := by
    simpa [prefixWord, tailWord_2883058, baseEnd_2883058] using wordTrace_append hprefix tailTrace_2883058
  have hstable : (prefixWord ++ tailWord_2883058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883058).length < 2 ^ (prefixWord ++ tailWord_2883058).sum := by decide
  have hdescent : baseEnd_2883058 < baseStart_2883058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883197 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_2883197 : Nat := 118140960795 + 2883197 * 2 ^ 59
def prefixEnd_2883197 : Nat := 4983230072969 + 3 ^ 40 * 2883197 * 2
def baseEnd_2883197 : Nat := 986977255067507474785283

theorem tailTrace_2883197 : CollatzResearch.WordTrace tailWord_2883197 prefixEnd_2883197 986977255067507474785283 := by
  unfold tailWord_2883197
  simp only [CollatzResearch.WordTrace]
  refine ⟨105158833735677154689879845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70105889157118103126586563 105158833735677154689879845)
  ·
    refine ⟨19717281325439466504352471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105158833735677154689879845 19717281325439466504352471)
    ·
      refine ⟨29575921988159199756528707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19717281325439466504352471 29575921988159199756528707)
      ·
        refine ⟨44363882982238799634793061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29575921988159199756528707 44363882982238799634793061)
        ·
          refine ⟨8318228059169774931523699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44363882982238799634793061 8318228059169774931523699)
          ·
            refine ⟨12477342088754662397285549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8318228059169774931523699 12477342088754662397285549)
            ·
              refine ⟨4679003283282998398982081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12477342088754662397285549 4679003283282998398982081)
              ·
                refine ⟨3509252462462248799236561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4679003283282998398982081 3509252462462248799236561)
                ·
                  refine ⟨2631939346846686599427421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3509252462462248799236561 2631939346846686599427421)
                  ·
                    refine ⟨986977255067507474785283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2631939346846686599427421 986977255067507474785283)
                    ·
                      rfl

theorem cell22_2883197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_2883197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883197 prefixEnd_2883197 := by exact prefixLift 2883197
  have htrace : WordTrace (prefixWord ++ tailWord_2883197) baseStart_2883197 baseEnd_2883197 := by
    simpa [prefixWord, tailWord_2883197, baseEnd_2883197] using wordTrace_append hprefix tailTrace_2883197
  have hstable : (prefixWord ++ tailWord_2883197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883197).length < 2 ^ (prefixWord ++ tailWord_2883197).sum := by decide
  have hdescent : baseEnd_2883197 < baseStart_2883197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883214 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_2883214 : Nat := 118140960795 + 2883214 * 2 ^ 59
def prefixEnd_2883214 : Nat := 4983230072969 + 3 ^ 40 * 2883214 * 2
def baseEnd_2883214 : Nat := 986983074514925097110231

theorem tailTrace_2883214 : CollatzResearch.WordTrace tailWord_2883214 prefixEnd_2883214 986983074514925097110231 := by
  unfold tailWord_2883214
  simp only [CollatzResearch.WordTrace]
  refine ⟨13144931722076945824156087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70106302517743711062165797 13144931722076945824156087)
  ·
    refine ⟨19717397583115418736234131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13144931722076945824156087 19717397583115418736234131)
    ·
      refine ⟨29576096374673128104351197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19717397583115418736234131 29576096374673128104351197)
      ·
        refine ⟨11091036140502423039131699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29576096374673128104351197 11091036140502423039131699)
        ·
          refine ⟨16636554210753634558697549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11091036140502423039131699 16636554210753634558697549)
          ·
            refine ⟨6238707829032612959511581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16636554210753634558697549 6238707829032612959511581)
            ·
              refine ⟨2339515435887229859816843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6238707829032612959511581 2339515435887229859816843)
              ·
                refine ⟨3509273153830844789725265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2339515435887229859816843 3509273153830844789725265)
                ·
                  refine ⟨2631954865373133592293949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3509273153830844789725265 2631954865373133592293949)
                  ·
                    refine ⟨986983074514925097110231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2631954865373133592293949 986983074514925097110231)
                    ·
                      rfl

theorem cell22_2883214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_2883214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883214 prefixEnd_2883214 := by exact prefixLift 2883214
  have htrace : WordTrace (prefixWord ++ tailWord_2883214) baseStart_2883214 baseEnd_2883214 := by
    simpa [prefixWord, tailWord_2883214, baseEnd_2883214] using wordTrace_append hprefix tailTrace_2883214
  have hstable : (prefixWord ++ tailWord_2883214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883214).length < 2 ^ (prefixWord ++ tailWord_2883214).sum := by decide
  have hdescent : baseEnd_2883214 < baseStart_2883214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883315 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 4, 3]
def baseStart_2883315 : Nat := 118140960795 + 2883315 * 2 ^ 59
def prefixEnd_2883315 : Nat := 4983230072969 + 3 ^ 40 * 2883315 * 2
def baseEnd_2883315 : Nat := 987017648878994500334921

theorem tailTrace_2883315 : CollatzResearch.WordTrace tailWord_2883315 prefixEnd_2883315 987017648878994500334921 := by
  unfold tailWord_2883315
  simp only [CollatzResearch.WordTrace]
  refine ⟨105163137549249660842675399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70108758366166440561783599 105163137549249660842675399)
  ·
    refine ⟨157744706323874491264013099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105163137549249660842675399 157744706323874491264013099)
    ·
      refine ⟨236617059485811736896019649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157744706323874491264013099 236617059485811736896019649)
      ·
        refine ⟨177462794614358802672014737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236617059485811736896019649 177462794614358802672014737)
        ·
          refine ⟨133097095960769102004011053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177462794614358802672014737 133097095960769102004011053)
          ·
            refine ⟨49911410985288413251504145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 133097095960769102004011053 49911410985288413251504145)
            ·
              refine ⟨37433558238966309938628109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49911410985288413251504145 37433558238966309938628109)
              ·
                refine ⟨14037584339612366226985541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37433558238966309938628109 14037584339612366226985541)
                ·
                  refine ⟨2632047063677318667559789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14037584339612366226985541 2632047063677318667559789)
                  ·
                    refine ⟨987017648878994500334921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632047063677318667559789 987017648878994500334921)
                    ·
                      rfl

theorem cell22_2883315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 4, 3].length) (baseStart_2883315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883315 prefixEnd_2883315 := by exact prefixLift 2883315
  have htrace : WordTrace (prefixWord ++ tailWord_2883315) baseStart_2883315 baseEnd_2883315 := by
    simpa [prefixWord, tailWord_2883315, baseEnd_2883315] using wordTrace_append hprefix tailTrace_2883315
  have hstable : (prefixWord ++ tailWord_2883315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883315).length < 2 ^ (prefixWord ++ tailWord_2883315).sum := by decide
  have hdescent : baseEnd_2883315 < baseStart_2883315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883332 : List Nat := [2, 3, 2, 2, 1, 3, 2, 1, 1, 5]
def baseStart_2883332 : Nat := 118140960795 + 2883332 * 2 ^ 59
def prefixEnd_2883332 : Nat := 4983230072969 + 3 ^ 40 * 2883332 * 2
def baseEnd_2883332 : Nat := 987023468326412122659869

theorem tailTrace_2883332 : CollatzResearch.WordTrace tailWord_2883332 prefixEnd_2883332 987023468326412122659869 := by
  unfold tailWord_2883332
  simp only [CollatzResearch.WordTrace]
  refine ⟨52581878795094036373022125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70109171726792048497362833 52581878795094036373022125)
  ·
    refine ⟨19718204548160263639883297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52581878795094036373022125 19718204548160263639883297)
    ·
      refine ⟨14788653411120197729912473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19718204548160263639883297 14788653411120197729912473)
      ·
        refine ⟨11091490058340148297434355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14788653411120197729912473 11091490058340148297434355)
        ·
          refine ⟨16637235087510222446151533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11091490058340148297434355 16637235087510222446151533)
          ·
            refine ⟨6238963157816333417306825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16637235087510222446151533 6238963157816333417306825)
            ·
              refine ⟨4679222368362250062980119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6238963157816333417306825 4679222368362250062980119)
              ·
                refine ⟨7018833552543375094470179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4679222368362250062980119 7018833552543375094470179)
                ·
                  refine ⟨10528250328815062641705269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7018833552543375094470179 10528250328815062641705269)
                  ·
                    refine ⟨987023468326412122659869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10528250328815062641705269 987023468326412122659869)
                    ·
                      rfl

theorem cell22_2883332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_2883332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883332 prefixEnd_2883332 := by exact prefixLift 2883332
  have htrace : WordTrace (prefixWord ++ tailWord_2883332) baseStart_2883332 baseEnd_2883332 := by
    simpa [prefixWord, tailWord_2883332, baseEnd_2883332] using wordTrace_append hprefix tailTrace_2883332
  have hstable : (prefixWord ++ tailWord_2883332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883332).length < 2 ^ (prefixWord ++ tailWord_2883332).sum := by decide
  have hdescent : baseEnd_2883332 < baseStart_2883332 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883343 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 1, 9]
def baseStart_2883343 : Nat := 118140960795 + 2883343 * 2 ^ 59
def prefixEnd_2883343 : Nat := 4983230072969 + 3 ^ 40 * 2883343 * 2
def baseEnd_2883343 : Nat := 987027233851211760634835

theorem tailTrace_2883343 : CollatzResearch.WordTrace tailWord_2883343 prefixEnd_2883343 987027233851211760634835 := by
  unfold tailWord_2883343
  simp only [CollatzResearch.WordTrace]
  refine ⟨105164158793148221624694683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70109439195432147749796455 105164158793148221624694683)
  ·
    refine ⟨157746238189722332437042025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105164158793148221624694683 157746238189722332437042025)
    ·
      refine ⟨118309678642291749327781519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157746238189722332437042025 118309678642291749327781519)
      ·
        refine ⟨177464517963437623991672279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118309678642291749327781519 177464517963437623991672279)
        ·
          refine ⟨266196776945156435987508419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177464517963437623991672279 266196776945156435987508419)
          ·
            refine ⟨399295165417734653981262629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266196776945156435987508419 399295165417734653981262629)
            ·
              refine ⟨74867843515825247621486743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 399295165417734653981262629 74867843515825247621486743)
              ·
                refine ⟨112301765273737871432230115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74867843515825247621486743 112301765273737871432230115)
                ·
                  refine ⟨168452647910606807148345173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112301765273737871432230115 168452647910606807148345173)
                  ·
                    refine ⟨987027233851211760634835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 168452647910606807148345173 987027233851211760634835)
                    ·
                      rfl

theorem cell22_2883343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_2883343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883343 prefixEnd_2883343 := by exact prefixLift 2883343
  have htrace : WordTrace (prefixWord ++ tailWord_2883343) baseStart_2883343 baseEnd_2883343 := by
    simpa [prefixWord, tailWord_2883343, baseEnd_2883343] using wordTrace_append hprefix tailTrace_2883343
  have hstable : (prefixWord ++ tailWord_2883343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883343).length < 2 ^ (prefixWord ++ tailWord_2883343).sum := by decide
  have hdescent : baseEnd_2883343 < baseStart_2883343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883377 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 3, 3]
def baseStart_2883377 : Nat := 118140960795 + 2883377 * 2 ^ 59
def prefixEnd_2883377 : Nat := 4983230072969 + 3 ^ 40 * 2883377 * 2
def baseEnd_2883377 : Nat := 987038872746047005284731

theorem tailTrace_2883377 : CollatzResearch.WordTrace tailWord_2883377 prefixEnd_2883377 987038872746047005284731 := by
  unfold tailWord_2883377
  simp only [CollatzResearch.WordTrace]
  refine ⟨105165398875025045431432385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70110265916683363620954923 105165398875025045431432385)
  ·
    refine ⟨78874049156268784073574289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105165398875025045431432385 78874049156268784073574289)
    ·
      refine ⟨59155536867201588055180717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78874049156268784073574289 59155536867201588055180717)
      ·
        refine ⟨22183326325200595520692769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59155536867201588055180717 22183326325200595520692769)
        ·
          refine ⟨16637494743900446640519577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22183326325200595520692769 16637494743900446640519577)
          ·
            refine ⟨12478121057925334980389683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16637494743900446640519577 12478121057925334980389683)
            ·
              refine ⟨18717181586888002470584525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12478121057925334980389683 18717181586888002470584525)
              ·
                refine ⟨7018943095083000926469197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18717181586888002470584525 7018943095083000926469197)
                ·
                  refine ⟨2632103660656125347425949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7018943095083000926469197 2632103660656125347425949)
                  ·
                    refine ⟨987038872746047005284731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632103660656125347425949 987038872746047005284731)
                    ·
                      rfl

theorem cell22_2883377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 3, 3].length) (baseStart_2883377 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883377 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883377 prefixEnd_2883377 := by exact prefixLift 2883377
  have htrace : WordTrace (prefixWord ++ tailWord_2883377) baseStart_2883377 baseEnd_2883377 := by
    simpa [prefixWord, tailWord_2883377, baseEnd_2883377] using wordTrace_append hprefix tailTrace_2883377
  have hstable : (prefixWord ++ tailWord_2883377).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883377).length < 2 ^ (prefixWord ++ tailWord_2883377).sum := by decide
  have hdescent : baseEnd_2883377 < baseStart_2883377 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883428 : List Nat := [2, 3, 1, 1, 5, 1, 3, 2, 1, 3]
def baseStart_2883428 : Nat := 118140960795 + 2883428 * 2 ^ 59
def prefixEnd_2883428 : Nat := 4983230072969 + 3 ^ 40 * 2883428 * 2
def baseEnd_2883428 : Nat := 987056331088299872259575

theorem tailTrace_2883428 : CollatzResearch.WordTrace tailWord_2883428 prefixEnd_2883428 987056331088299872259575 := by
  unfold tailWord_2883428
  simp only [CollatzResearch.WordTrace]
  refine ⟨52583629498920140570769469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70111505998560187427692625 52583629498920140570769469)
  ·
    refine ⟨19718861062095052714038551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52583629498920140570769469 19718861062095052714038551)
    ·
      refine ⟨29578291593142579071057827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19718861062095052714038551 29578291593142579071057827)
      ·
        refine ⟨44367437389713868606586741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29578291593142579071057827 44367437389713868606586741)
        ·
          refine ⟨4159447255285675181867507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44367437389713868606586741 4159447255285675181867507)
          ·
            refine ⟨6239170882928512772801261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4159447255285675181867507 6239170882928512772801261)
            ·
              refine ⟨2339689081098192289800473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6239170882928512772801261 2339689081098192289800473)
              ·
                refine ⟨1754766810823644217350355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2339689081098192289800473 1754766810823644217350355)
                ·
                  refine ⟨2632150216235466326025533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754766810823644217350355 2632150216235466326025533)
                  ·
                    refine ⟨987056331088299872259575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632150216235466326025533 987056331088299872259575)
                    ·
                      rfl

theorem cell22_2883428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 1, 3].length) (baseStart_2883428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883428 prefixEnd_2883428 := by exact prefixLift 2883428
  have htrace : WordTrace (prefixWord ++ tailWord_2883428) baseStart_2883428 baseEnd_2883428 := by
    simpa [prefixWord, tailWord_2883428, baseEnd_2883428] using wordTrace_append hprefix tailTrace_2883428
  have hstable : (prefixWord ++ tailWord_2883428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883428).length < 2 ^ (prefixWord ++ tailWord_2883428).sum := by decide
  have hdescent : baseEnd_2883428 < baseStart_2883428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883546 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 3, 3]
def baseStart_2883546 : Nat := 118140960795 + 2883546 * 2 ^ 59
def prefixEnd_2883546 : Nat := 4983230072969 + 3 ^ 40 * 2883546 * 2
def baseEnd_2883546 : Nat := 987096724899786897809213

theorem tailTrace_2883546 : CollatzResearch.WordTrace tailWord_2883546 prefixEnd_2883546 987096724899786897809213 := by
  unfold tailWord_2883546
  simp only [CollatzResearch.WordTrace]
  refine ⟨26292890702853196823583623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70114375207608524862889661 26292890702853196823583623)
  ·
    refine ⟨39439336054279795235375435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26292890702853196823583623 39439336054279795235375435)
    ·
      refine ⟨59159004081419692853063153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39439336054279795235375435 59159004081419692853063153)
      ·
        refine ⟨44369253061064769639797365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59159004081419692853063153 44369253061064769639797365)
        ·
          refine ⟨4159617474474822153731003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44369253061064769639797365 4159617474474822153731003)
          ·
            refine ⟨6239426211712233230596505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4159617474474822153731003 6239426211712233230596505)
            ·
              refine ⟨4679569658784174922947379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6239426211712233230596505 4679569658784174922947379)
              ·
                refine ⟨7019354488176262384421069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4679569658784174922947379 7019354488176262384421069)
                ·
                  refine ⟨2632257933066098394157901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7019354488176262384421069 2632257933066098394157901)
                  ·
                    refine ⟨987096724899786897809213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632257933066098394157901 987096724899786897809213)
                    ·
                      rfl

theorem cell22_2883546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 3, 3].length) (baseStart_2883546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883546 prefixEnd_2883546 := by exact prefixLift 2883546
  have htrace : WordTrace (prefixWord ++ tailWord_2883546) baseStart_2883546 baseEnd_2883546 := by
    simpa [prefixWord, tailWord_2883546, baseEnd_2883546] using wordTrace_append hprefix tailTrace_2883546
  have hstable : (prefixWord ++ tailWord_2883546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883546).length < 2 ^ (prefixWord ++ tailWord_2883546).sum := by decide
  have hdescent : baseEnd_2883546 < baseStart_2883546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883589 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 1, 4]
def baseStart_2883589 : Nat := 118140960795 + 2883589 * 2 ^ 59
def prefixEnd_2883589 : Nat := 4983230072969 + 3 ^ 40 * 2883589 * 2
def baseEnd_2883589 : Nat := 987111444678549118984081

theorem tailTrace_2883589 : CollatzResearch.WordTrace tailWord_2883589 prefixEnd_2883589 987111444678549118984081 := by
  unfold tailWord_2883589
  simp only [CollatzResearch.WordTrace]
  refine ⟨105173131150257005638149821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70115420766838003758766547 105173131150257005638149821)
  ·
    refine ⟨39439924181346377114306183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105173131150257005638149821 39439924181346377114306183)
    ·
      refine ⟨59159886272019565671459275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39439924181346377114306183 59159886272019565671459275)
      ·
        refine ⟨88739829408029348507188913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59159886272019565671459275 88739829408029348507188913)
        ·
          refine ⟨66554872056022011380391685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88739829408029348507188913 66554872056022011380391685)
          ·
            refine ⟨12479038510504127133823441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66554872056022011380391685 12479038510504127133823441)
            ·
              refine ⟨9359278882878095350367581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12479038510504127133823441 9359278882878095350367581)
              ·
                refine ⟨3509729581079285756387843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9359278882878095350367581 3509729581079285756387843)
                ·
                  refine ⟨5264594371618928634581765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3509729581079285756387843 5264594371618928634581765)
                  ·
                    refine ⟨987111444678549118984081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5264594371618928634581765 987111444678549118984081)
                    ·
                      rfl

theorem cell22_2883589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 1, 4].length) (baseStart_2883589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883589 prefixEnd_2883589 := by exact prefixLift 2883589
  have htrace : WordTrace (prefixWord ++ tailWord_2883589) baseStart_2883589 baseEnd_2883589 := by
    simpa [prefixWord, tailWord_2883589, baseEnd_2883589] using wordTrace_append hprefix tailTrace_2883589
  have hstable : (prefixWord ++ tailWord_2883589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883589).length < 2 ^ (prefixWord ++ tailWord_2883589).sum := by decide
  have hdescent : baseEnd_2883589 < baseStart_2883589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883597 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 3, 3]
def baseStart_2883597 : Nat := 118140960795 + 2883597 * 2 ^ 59
def prefixEnd_2883597 : Nat := 4983230072969 + 3 ^ 40 * 2883597 * 2
def baseEnd_2883597 : Nat := 987114183242039764784057

theorem tailTrace_2883597 : CollatzResearch.WordTrace tailWord_2883597 prefixEnd_2883597 987114183242039764784057 := by
  unfold tailWord_2883597
  simp only [CollatzResearch.WordTrace]
  refine ⟨105173422934228023004441045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70115615289485348669627363 105173422934228023004441045)
  ·
    refine ⟨2465002100020969289166587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 105173422934228023004441045 2465002100020969289166587)
    ·
      refine ⟨3697503150031453933749881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2465002100020969289166587 3697503150031453933749881)
      ·
        refine ⟨2773127362523590450312411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3697503150031453933749881 2773127362523590450312411)
        ·
          refine ⟨4159691043785385675468617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773127362523590450312411 4159691043785385675468617)
          ·
            refine ⟨3119768282839039256601463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4159691043785385675468617 3119768282839039256601463)
            ·
              refine ⟨4679652424258558884902195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119768282839039256601463 4679652424258558884902195)
              ·
                refine ⟨7019478636387838327353293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4679652424258558884902195 7019478636387838327353293)
                ·
                  refine ⟨2632304488645439372757485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7019478636387838327353293 2632304488645439372757485)
                  ·
                    refine ⟨987114183242039764784057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632304488645439372757485 987114183242039764784057)
                    ·
                      rfl

theorem cell22_2883597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_2883597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883597 prefixEnd_2883597 := by exact prefixLift 2883597
  have htrace : WordTrace (prefixWord ++ tailWord_2883597) baseStart_2883597 baseEnd_2883597 := by
    simpa [prefixWord, tailWord_2883597, baseEnd_2883597] using wordTrace_append hprefix tailTrace_2883597
  have hstable : (prefixWord ++ tailWord_2883597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883597).length < 2 ^ (prefixWord ++ tailWord_2883597).sum := by decide
  have hdescent : baseEnd_2883597 < baseStart_2883597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883632 : List Nat := [2, 1, 1, 1, 2, 5, 2, 8]
def baseStart_2883632 : Nat := 118140960795 + 2883632 * 2 ^ 59
def prefixEnd_2883632 : Nat := 4983230072969 + 3 ^ 40 * 2883632 * 2
def baseEnd_2883632 : Nat := 109680684939701260017661

theorem tailTrace_2883632 : CollatzResearch.WordTrace tailWord_2883632 prefixEnd_2883632 109680684939701260017661 := by
  unfold tailWord_2883632
  simp only [CollatzResearch.WordTrace]
  refine ⟨52587349744550611990982575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70116466326067482654643433 52587349744550611990982575)
  ·
    refine ⟨78881024616825917986473863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52587349744550611990982575 78881024616825917986473863)
    ·
      refine ⟨118321536925238876979710795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78881024616825917986473863 118321536925238876979710795)
      ·
        refine ⟨177482305387858315469566193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118321536925238876979710795 177482305387858315469566193)
        ·
          refine ⟨133111729040893736602174645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177482305387858315469566193 133111729040893736602174645)
          ·
            refine ⟨12479224597583787806453873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 133111729040893736602174645 12479224597583787806453873)
            ·
              refine ⟨9359418448187840854840405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12479224597583787806453873 9359418448187840854840405)
              ·
                refine ⟨109680684939701260017661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9359418448187840854840405 109680684939701260017661)
                ·
                  rfl

theorem cell22_2883632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 8].length) (baseStart_2883632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883632 prefixEnd_2883632 := by exact prefixLift 2883632
  have htrace : WordTrace (prefixWord ++ tailWord_2883632) baseStart_2883632 baseEnd_2883632 := by
    simpa [prefixWord, tailWord_2883632, baseEnd_2883632] using wordTrace_append hprefix tailTrace_2883632
  have hstable : (prefixWord ++ tailWord_2883632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883632).length < 2 ^ (prefixWord ++ tailWord_2883632).sum := by decide
  have hdescent : baseEnd_2883632 < baseStart_2883632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883634 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 2, 4]
def baseStart_2883634 : Nat := 118140960795 + 2883634 * 2 ^ 59
def prefixEnd_2883634 : Nat := 4983230072969 + 3 ^ 40 * 2883634 * 2
def baseEnd_2883634 : Nat := 987126849098184001608943

theorem tailTrace_2883634 : CollatzResearch.WordTrace tailWord_2883634 prefixEnd_2883634 987126849098184001608943 := by
  unfold tailWord_2883634
  simp only [CollatzResearch.WordTrace]
  refine ⟨26293693108773494580884489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70116514956729318882358637 26293693108773494580884489)
  ·
    refine ⟨19720269831580120935663367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26293693108773494580884489 19720269831580120935663367)
    ·
      refine ⟨29580404747370181403495051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19720269831580120935663367 29580404747370181403495051)
      ·
        refine ⟨44370607121055272105242577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29580404747370181403495051 44370607121055272105242577)
        ·
          refine ⟨33277955340791454078931933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44370607121055272105242577 33277955340791454078931933)
          ·
            refine ⟨12479233252796795279599475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33277955340791454078931933 12479233252796795279599475)
            ·
              refine ⟨18718849879195192919399213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12479233252796795279599475 18718849879195192919399213)
              ·
                refine ⟨7019568704698197344774705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18718849879195192919399213 7019568704698197344774705)
                ·
                  refine ⟨5264676528523648008581029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7019568704698197344774705 5264676528523648008581029)
                  ·
                    refine ⟨987126849098184001608943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5264676528523648008581029 987126849098184001608943)
                    ·
                      rfl

theorem cell22_2883634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_2883634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883634 prefixEnd_2883634 := by exact prefixLift 2883634
  have htrace : WordTrace (prefixWord ++ tailWord_2883634) baseStart_2883634 baseEnd_2883634 := by
    simpa [prefixWord, tailWord_2883634, baseEnd_2883634] using wordTrace_append hprefix tailTrace_2883634
  have hstable : (prefixWord ++ tailWord_2883634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883634).length < 2 ^ (prefixWord ++ tailWord_2883634).sum := by decide
  have hdescent : baseEnd_2883634 < baseStart_2883634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883666 : List Nat := [3, 2, 2, 1, 4, 2, 1, 7]
def baseStart_2883666 : Nat := 118140960795 + 2883666 * 2 ^ 59
def prefixEnd_2883666 : Nat := 4983230072969 + 3 ^ 40 * 2883666 * 2
def baseEnd_2883666 : Nat := 109681978150238509423205

theorem tailTrace_2883666 : CollatzResearch.WordTrace tailWord_2883666 prefixEnd_2883666 109681978150238509423205 := by
  unfold tailWord_2883666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26293984892744511947175713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70117293047318698525801901 26293984892744511947175713)
  ·
    refine ⟨19720488669558383960381785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26293984892744511947175713 19720488669558383960381785)
    ·
      refine ⟨14790366502168787970286339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19720488669558383960381785 14790366502168787970286339)
      ·
        refine ⟨22185549753253181955429509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14790366502168787970286339 22185549753253181955429509)
        ·
          refine ⟨4159790578734971616643033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22185549753253181955429509 4159790578734971616643033)
          ·
            refine ⟨3119842934051228712482275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4159790578734971616643033 3119842934051228712482275)
            ·
              refine ⟨4679764401076843068723413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3119842934051228712482275 4679764401076843068723413)
              ·
                refine ⟨109681978150238509423205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4679764401076843068723413 109681978150238509423205)
                ·
                  rfl

theorem cell22_2883666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 7].length) (baseStart_2883666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883666 prefixEnd_2883666 := by exact prefixLift 2883666
  have htrace : WordTrace (prefixWord ++ tailWord_2883666) baseStart_2883666 baseEnd_2883666 := by
    simpa [prefixWord, tailWord_2883666, baseEnd_2883666] using wordTrace_append hprefix tailTrace_2883666
  have hstable : (prefixWord ++ tailWord_2883666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883666).length < 2 ^ (prefixWord ++ tailWord_2883666).sum := by decide
  have hdescent : baseEnd_2883666 < baseStart_2883666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883670 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 2, 3]
def baseStart_2883670 : Nat := 118140960795 + 2883670 * 2 ^ 59
def prefixEnd_2883670 : Nat := 4983230072969 + 3 ^ 40 * 2883670 * 2
def baseEnd_2883670 : Nat := 987139172633891907708833

theorem tailTrace_2883670 : CollatzResearch.WordTrace tailWord_2883670 prefixEnd_2883670 987139172633891907708833 := by
  unfold tailWord_2883670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573505341435222279490529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70117390308642370981232309 6573505341435222279490529)
  ·
    refine ⟨4930129006076416709617897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6573505341435222279490529 4930129006076416709617897)
    ·
      refine ⟨3697596754557312532213423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4930129006076416709617897 3697596754557312532213423)
      ·
        refine ⟨5546395131835968798320135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3697596754557312532213423 5546395131835968798320135)
        ·
          refine ⟨8319592697753953197480203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5546395131835968798320135 8319592697753953197480203)
          ·
            refine ⟨12479389046630929796220305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8319592697753953197480203 12479389046630929796220305)
            ·
              refine ⟨9359541784973197347165229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12479389046630929796220305 9359541784973197347165229)
              ·
                refine ⟨3509828169364949005186961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9359541784973197347165229 3509828169364949005186961)
                ·
                  refine ⟨2632371127023711753890221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3509828169364949005186961 2632371127023711753890221)
                  ·
                    refine ⟨987139172633891907708833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632371127023711753890221 987139172633891907708833)
                    ·
                      rfl

theorem cell22_2883670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_2883670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883670 prefixEnd_2883670 := by exact prefixLift 2883670
  have htrace : WordTrace (prefixWord ++ tailWord_2883670) baseStart_2883670 baseEnd_2883670 := by
    simpa [prefixWord, tailWord_2883670, baseEnd_2883670] using wordTrace_append hprefix tailTrace_2883670
  have hstable : (prefixWord ++ tailWord_2883670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883670).length < 2 ^ (prefixWord ++ tailWord_2883670).sum := by decide
  have hdescent : baseEnd_2883670 < baseStart_2883670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883694 : List Nat := [4, 1, 2, 2, 1, 1, 2, 2, 7]
def baseStart_2883694 : Nat := 118140960795 + 2883694 * 2 ^ 59
def prefixEnd_2883694 : Nat := 4983230072969 + 3 ^ 40 * 2883694 * 2
def baseEnd_2883694 : Nat := 329049129441454615036253

theorem tailTrace_2883694 : CollatzResearch.WordTrace tailWord_2883694 prefixEnd_2883694 329049129441454615036253 := by
  unfold tailWord_2883694
  simp only [CollatzResearch.WordTrace]
  refine ⟨13147120101859576071340267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70117973876584405713814757 13147120101859576071340267)
  ·
    refine ⟨19720680152789364107010401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13147120101859576071340267 19720680152789364107010401)
    ·
      refine ⟨14790510114592023080257801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19720680152789364107010401 14790510114592023080257801)
      ·
        refine ⟨11092882585944017310193351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14790510114592023080257801 11092882585944017310193351)
        ·
          refine ⟨16639323878916025965290027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11092882585944017310193351 16639323878916025965290027)
          ·
            refine ⟨24958985818374038947935041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16639323878916025965290027 24958985818374038947935041)
            ·
              refine ⟨18719239363780529210951281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24958985818374038947935041 18719239363780529210951281)
              ·
                refine ⟨14039429522835396908213461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18719239363780529210951281 14039429522835396908213461)
                ·
                  refine ⟨329049129441454615036253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14039429522835396908213461 329049129441454615036253)
                  ·
                    rfl

theorem cell22_2883694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_2883694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883694 prefixEnd_2883694 := by exact prefixLift 2883694
  have htrace : WordTrace (prefixWord ++ tailWord_2883694) baseStart_2883694 baseEnd_2883694 := by
    simpa [prefixWord, tailWord_2883694, baseEnd_2883694] using wordTrace_append hprefix tailTrace_2883694
  have hstable : (prefixWord ++ tailWord_2883694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883694).length < 2 ^ (prefixWord ++ tailWord_2883694).sum := by decide
  have hdescent : baseEnd_2883694 < baseStart_2883694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883698 : List Nat := [3, 2, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_2883698 : Nat := 118140960795 + 2883698 * 2 ^ 59
def prefixEnd_2883698 : Nat := 4983230072969 + 3 ^ 40 * 2883698 * 2
def baseEnd_2883698 : Nat := 987148757606109168008747

theorem tailTrace_2883698 : CollatzResearch.WordTrace tailWord_2883698 prefixEnd_2883698 987148757606109168008747 := by
  unfold tailWord_2883698
  simp only [CollatzResearch.WordTrace]
  refine ⟨26294276676715529313466937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70118071137908078169245165 26294276676715529313466937)
  ·
    refine ⟨19720707507536646985100203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26294276676715529313466937 19720707507536646985100203)
    ·
      refine ⟨29581061261304970477650305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19720707507536646985100203 29581061261304970477650305)
      ·
        refine ⟨22185795945978727858237729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29581061261304970477650305 22185795945978727858237729)
        ·
          refine ⟨16639346959484045893678297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22185795945978727858237729 16639346959484045893678297)
          ·
            refine ⟨12479510219613034420258723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16639346959484045893678297 12479510219613034420258723)
            ·
              refine ⟨18719265329419551630388085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12479510219613034420258723 18719265329419551630388085)
              ·
                refine ⟨1754931124633082965348883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18719265329419551630388085 1754931124633082965348883)
                ·
                  refine ⟨2632396686949624448023325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1754931124633082965348883 2632396686949624448023325)
                  ·
                    refine ⟨987148757606109168008747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632396686949624448023325 987148757606109168008747)
                    ·
                      rfl

theorem cell22_2883698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_2883698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883698 prefixEnd_2883698 := by exact prefixLift 2883698
  have htrace : WordTrace (prefixWord ++ tailWord_2883698) baseStart_2883698 baseEnd_2883698 := by
    simpa [prefixWord, tailWord_2883698, baseEnd_2883698] using wordTrace_append hprefix tailTrace_2883698
  have hstable : (prefixWord ++ tailWord_2883698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883698).length < 2 ^ (prefixWord ++ tailWord_2883698).sum := by decide
  have hdescent : baseEnd_2883698 < baseStart_2883698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883709 : List Nat := [1, 4, 1, 1, 3, 2, 1, 2, 2, 5]
def baseStart_2883709 : Nat := 118140960795 + 2883709 * 2 ^ 59
def prefixEnd_2883709 : Nat := 4983230072969 + 3 ^ 40 * 2883709 * 2
def baseEnd_2883709 : Nat := 987152523130908805983713

theorem tailTrace_2883709 : CollatzResearch.WordTrace tailWord_2883709 prefixEnd_2883709 987152523130908805983713 := by
  unfold tailWord_2883709
  simp only [CollatzResearch.WordTrace]
  refine ⟨105177507909822266132518181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70118338606548177421678787 105177507909822266132518181)
  ·
    refine ⟨19720782733091674899847159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105177507909822266132518181 19720782733091674899847159)
    ·
      refine ⟨29581174099637512349770739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19720782733091674899847159 29581174099637512349770739)
      ·
        refine ⟨44371761149456268524656109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29581174099637512349770739 44371761149456268524656109)
        ·
          refine ⟨16639410431046100696746041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44371761149456268524656109 16639410431046100696746041)
          ·
            refine ⟨12479557823284575522559531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16639410431046100696746041 12479557823284575522559531)
            ·
              refine ⟨18719336734926863283839297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12479557823284575522559531 18719336734926863283839297)
              ·
                refine ⟨14039502551195147462879473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18719336734926863283839297 14039502551195147462879473)
                ·
                  refine ⟨10529626913396360597159605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14039502551195147462879473 10529626913396360597159605)
                  ·
                    refine ⟨987152523130908805983713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10529626913396360597159605 987152523130908805983713)
                    ·
                      rfl

theorem cell22_2883709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 1, 2, 2, 5].length) (baseStart_2883709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883709 prefixEnd_2883709 := by exact prefixLift 2883709
  have htrace : WordTrace (prefixWord ++ tailWord_2883709) baseStart_2883709 baseEnd_2883709 := by
    simpa [prefixWord, tailWord_2883709, baseEnd_2883709] using wordTrace_append hprefix tailTrace_2883709
  have hstable : (prefixWord ++ tailWord_2883709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883709).length < 2 ^ (prefixWord ++ tailWord_2883709).sum := by decide
  have hdescent : baseEnd_2883709 < baseStart_2883709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883734 : List Nat := [5, 3, 2, 1, 1, 2, 2, 6]
def baseStart_2883734 : Nat := 118140960795 + 2883734 * 2 ^ 59
def prefixEnd_2883734 : Nat := 4983230072969 + 3 ^ 40 * 2883734 * 2
def baseEnd_2883734 : Nat := 109684564571313008234293

theorem tailTrace_2883734 : CollatzResearch.WordTrace tailWord_2883734 prefixEnd_2883734 109684564571313008234293 := by
  unfold tailWord_2883734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6573651233420730962636141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70118946489821130268118837 6573651233420730962636141)
  ·
    refine ⟨2465119212532774110988553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6573651233420730962636141 2465119212532774110988553)
    ·
      refine ⟨1848839409399580583241415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2465119212532774110988553 1848839409399580583241415)
      ·
        refine ⟨2773259114099370874862123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848839409399580583241415 2773259114099370874862123)
        ·
          refine ⟨4159888671149056312293185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773259114099370874862123 4159888671149056312293185)
          ·
            refine ⟨3119916503361792234219889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4159888671149056312293185 3119916503361792234219889)
            ·
              refine ⟨2339937377521344175664917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3119916503361792234219889 2339937377521344175664917)
              ·
                refine ⟨109684564571313008234293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2339937377521344175664917 109684564571313008234293)
                ·
                  rfl

theorem cell22_2883734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_2883734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883734 prefixEnd_2883734 := by exact prefixLift 2883734
  have htrace : WordTrace (prefixWord ++ tailWord_2883734) baseStart_2883734 baseEnd_2883734 := by
    simpa [prefixWord, tailWord_2883734, baseEnd_2883734] using wordTrace_append hprefix tailTrace_2883734
  have hstable : (prefixWord ++ tailWord_2883734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883734).length < 2 ^ (prefixWord ++ tailWord_2883734).sum := by decide
  have hdescent : baseEnd_2883734 < baseStart_2883734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883741 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 1, 4]
def baseStart_2883741 : Nat := 118140960795 + 2883741 * 2 ^ 59
def prefixEnd_2883741 : Nat := 4983230072969 + 3 ^ 40 * 2883741 * 2
def baseEnd_2883741 : Nat := 987163477384871389183615

theorem tailTrace_2883741 : CollatzResearch.WordTrace tailWord_2883741 prefixEnd_2883741 987163477384871389183615 := by
  unfold tailWord_2883741
  simp only [CollatzResearch.WordTrace]
  refine ⟨105178675045706335597683077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70119116697137557065122051 105178675045706335597683077)
  ·
    refine ⟨19721001571069937924565577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105178675045706335597683077 19721001571069937924565577)
    ·
      refine ⟨14790751178302453443424183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19721001571069937924565577 14790751178302453443424183)
      ·
        refine ⟨22186126767453680165136275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14790751178302453443424183 22186126767453680165136275)
        ·
          refine ⟨33279190151180520247704413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22186126767453680165136275 33279190151180520247704413)
          ·
            refine ⟨12479696306692695092889155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33279190151180520247704413 12479696306692695092889155)
            ·
              refine ⟨18719544460039042639333733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12479696306692695092889155 18719544460039042639333733)
              ·
                refine ⟨3509914586257320494875075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18719544460039042639333733 3509914586257320494875075)
                ·
                  refine ⟨5264871879385980742312613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3509914586257320494875075 5264871879385980742312613)
                  ·
                    refine ⟨987163477384871389183615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5264871879385980742312613 987163477384871389183615)
                    ·
                      rfl

theorem cell22_2883741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_2883741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883741 prefixEnd_2883741 := by exact prefixLift 2883741
  have htrace : WordTrace (prefixWord ++ tailWord_2883741) baseStart_2883741 baseEnd_2883741 := by
    simpa [prefixWord, tailWord_2883741, baseEnd_2883741] using wordTrace_append hprefix tailTrace_2883741
  have hstable : (prefixWord ++ tailWord_2883741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883741).length < 2 ^ (prefixWord ++ tailWord_2883741).sum := by decide
  have hdescent : baseEnd_2883741 < baseStart_2883741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883771 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 2, 3]
def baseStart_2883771 : Nat := 118140960795 + 2883771 * 2 ^ 59
def prefixEnd_2883771 : Nat := 4983230072969 + 3 ^ 40 * 2883771 * 2
def baseEnd_2883771 : Nat := 987173746997961310933523

theorem tailTrace_2883771 : CollatzResearch.WordTrace tailWord_2883771 prefixEnd_2883771 987173746997961310933523 := by
  unfold tailWord_2883771
  simp only [CollatzResearch.WordTrace]
  refine ⟨105179769235597650721275167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70119846157065100480850111 105179769235597650721275167)
  ·
    refine ⟨157769653853396476081912751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105179769235597650721275167 157769653853396476081912751)
    ·
      refine ⟨236654480780094714122869127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157769653853396476081912751 236654480780094714122869127)
      ·
        refine ⟨354981721170142071184303691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 236654480780094714122869127 354981721170142071184303691)
        ·
          refine ⟨532472581755213106776455537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 354981721170142071184303691 532472581755213106776455537)
          ·
            refine ⟨399354436316409830082341653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 532472581755213106776455537 399354436316409830082341653)
            ·
              refine ⟨18719739202331710785109765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 399354436316409830082341653 18719739202331710785109765)
              ·
                refine ⟨3509951100437195772208081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18719739202331710785109765 3509951100437195772208081)
                ·
                  refine ⟨2632463325327896829156061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3509951100437195772208081 2632463325327896829156061)
                  ·
                    refine ⟨987173746997961310933523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632463325327896829156061 987173746997961310933523)
                    ·
                      rfl

theorem cell22_2883771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 2, 3].length) (baseStart_2883771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883771 prefixEnd_2883771 := by exact prefixLift 2883771
  have htrace : WordTrace (prefixWord ++ tailWord_2883771) baseStart_2883771 baseEnd_2883771 := by
    simpa [prefixWord, tailWord_2883771, baseEnd_2883771] using wordTrace_append hprefix tailTrace_2883771
  have hstable : (prefixWord ++ tailWord_2883771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883771).length < 2 ^ (prefixWord ++ tailWord_2883771).sum := by decide
  have hdescent : baseEnd_2883771 < baseStart_2883771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883880 : List Nat := [2, 1, 5, 1, 3, 2, 1, 2, 5]
def baseStart_2883880 : Nat := 118140960795 + 2883880 * 2 ^ 59
def prefixEnd_2883880 : Nat := 4983230072969 + 3 ^ 40 * 2883880 * 2
def baseEnd_2883880 : Nat := 329070353308507119986063

theorem tailTrace_2883880 : CollatzResearch.WordTrace tailWord_2883880 prefixEnd_2883880 329070353308507119986063 := by
  unfold tailWord_2883880
  simp only [CollatzResearch.WordTrace]
  refine ⟨52591872396101381168496547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70122496528135174891328729 52591872396101381168496547)
  ·
    refine ⟨78887808594152071752744821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52591872396101381168496547 78887808594152071752744821)
    ·
      refine ⟨7395732055701756726819827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 78887808594152071752744821 7395732055701756726819827)
      ·
        refine ⟨11093598083552635090229741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395732055701756726819827 11093598083552635090229741)
        ·
          refine ⟨4160099281332238158836153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11093598083552635090229741 4160099281332238158836153)
          ·
            refine ⟨3120074460999178619127115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4160099281332238158836153 3120074460999178619127115)
            ·
              refine ⟨4680111691498767928690673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120074460999178619127115 4680111691498767928690673)
              ·
                refine ⟨3510083768624075946518005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4680111691498767928690673 3510083768624075946518005)
                ·
                  refine ⟨329070353308507119986063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3510083768624075946518005 329070353308507119986063)
                  ·
                    rfl

theorem cell22_2883880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 1, 2, 5].length) (baseStart_2883880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883880 prefixEnd_2883880 := by exact prefixLift 2883880
  have htrace : WordTrace (prefixWord ++ tailWord_2883880) baseStart_2883880 baseEnd_2883880 := by
    simpa [prefixWord, tailWord_2883880, baseEnd_2883880] using wordTrace_append hprefix tailTrace_2883880
  have hstable : (prefixWord ++ tailWord_2883880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883880).length < 2 ^ (prefixWord ++ tailWord_2883880).sum := by decide
  have hdescent : baseEnd_2883880 < baseStart_2883880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883891 : List Nat := [1, 1, 1, 2, 5, 1, 4, 1, 6]
def baseStart_2883891 : Nat := 118140960795 + 2883891 * 2 ^ 59
def prefixEnd_2883891 : Nat := 4983230072969 + 3 ^ 40 * 2883891 * 2
def baseEnd_2883891 : Nat := 329071608483440332644385

theorem tailTrace_2883891 : CollatzResearch.WordTrace tailWord_2883891 prefixEnd_2883891 329071608483440332644385 := by
  unfold tailWord_2883891
  simp only [CollatzResearch.WordTrace]
  refine ⟨105184145995162911215643527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70122763996775274143762351 105184145995162911215643527)
  ·
    refine ⟨157776218992744366823465291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105184145995162911215643527 157776218992744366823465291)
    ·
      refine ⟨236664328489116550235197937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157776218992744366823465291 236664328489116550235197937)
      ·
        refine ⟨177498246366837412676398453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236664328489116550235197937 177498246366837412676398453)
        ·
          refine ⟨16640460596891007438412355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177498246366837412676398453 16640460596891007438412355)
          ·
            refine ⟨24960690895336511157618533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16640460596891007438412355 24960690895336511157618533)
            ·
              refine ⟨4680129542875595842053475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24960690895336511157618533 4680129542875595842053475)
              ·
                refine ⟨7020194314313393763080213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680129542875595842053475 7020194314313393763080213)
                ·
                  refine ⟨329071608483440332644385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7020194314313393763080213 329071608483440332644385)
                  ·
                    rfl

theorem cell22_2883891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 4, 1, 6].length) (baseStart_2883891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883891 prefixEnd_2883891 := by exact prefixLift 2883891
  have htrace : WordTrace (prefixWord ++ tailWord_2883891) baseStart_2883891 baseEnd_2883891 := by
    simpa [prefixWord, tailWord_2883891, baseEnd_2883891] using wordTrace_append hprefix tailTrace_2883891
  have hstable : (prefixWord ++ tailWord_2883891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883891).length < 2 ^ (prefixWord ++ tailWord_2883891).sum := by decide
  have hdescent : baseEnd_2883891 < baseStart_2883891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883921 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 1, 6]
def baseStart_2883921 : Nat := 118140960795 + 2883921 * 2 ^ 59
def prefixEnd_2883921 : Nat := 4983230072969 + 3 ^ 40 * 2883921 * 2
def baseEnd_2883921 : Nat := 987225095063410919683063

theorem tailTrace_2883921 : CollatzResearch.WordTrace tailWord_2883921 prefixEnd_2883921 987225095063410919683063 := by
  unfold tailWord_2883921
  simp only [CollatzResearch.WordTrace]
  refine ⟨105185240185054226339235617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70123493456702817559490411 105185240185054226339235617)
  ·
    refine ⟨78888930138790669754426713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105185240185054226339235617 78888930138790669754426713)
    ·
      refine ⟨59166697604093002315820035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78888930138790669754426713 59166697604093002315820035)
      ·
        refine ⟨88750046406139503473730053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59166697604093002315820035 88750046406139503473730053)
        ·
          refine ⟨16640633701151156901324385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88750046406139503473730053 16640633701151156901324385)
          ·
            refine ⟨12480475275863367675993289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16640633701151156901324385 12480475275863367675993289)
            ·
              refine ⟨9360356456897525756994967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12480475275863367675993289 9360356456897525756994967)
              ·
                refine ⟨14040534685346288635492451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9360356456897525756994967 14040534685346288635492451)
                ·
                  refine ⟨21060802028019432953238677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14040534685346288635492451 21060802028019432953238677)
                  ·
                    refine ⟨987225095063410919683063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21060802028019432953238677 987225095063410919683063)
                    ·
                      rfl

theorem cell22_2883921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 6].length) (baseStart_2883921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883921 prefixEnd_2883921 := by exact prefixLift 2883921
  have htrace : WordTrace (prefixWord ++ tailWord_2883921) baseStart_2883921 baseEnd_2883921 := by
    simpa [prefixWord, tailWord_2883921, baseEnd_2883921] using wordTrace_append hprefix tailTrace_2883921
  have hstable : (prefixWord ++ tailWord_2883921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883921).length < 2 ^ (prefixWord ++ tailWord_2883921).sum := by decide
  have hdescent : baseEnd_2883921 < baseStart_2883921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883938 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2883938 : Nat := 118140960795 + 2883938 * 2 ^ 59
def prefixEnd_2883938 : Nat := 4983230072969 + 3 ^ 40 * 2883938 * 2
def baseEnd_2883938 : Nat := 987230914510828542008011

theorem tailTrace_2883938 : CollatzResearch.WordTrace tailWord_2883938 prefixEnd_2883938 987230914510828542008011 := by
  unfold tailWord_2883938
  simp only [CollatzResearch.WordTrace]
  refine ⟨26296465056498159560651117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70123906817328425495069645 26296465056498159560651117)
  ·
    refine ⟨9861174396186809835244169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26296465056498159560651117 9861174396186809835244169)
    ·
      refine ⟨7395880797140107376433127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9861174396186809835244169 7395880797140107376433127)
      ·
        refine ⟨11093821195710161064649691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395880797140107376433127 11093821195710161064649691)
        ·
          refine ⟨16640731793565241596974537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11093821195710161064649691 16640731793565241596974537)
          ·
            refine ⟨12480548845173931197730903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16640731793565241596974537 12480548845173931197730903)
            ·
              refine ⟨18720823267760896796596355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12480548845173931197730903 18720823267760896796596355)
              ·
                refine ⟨28081234901641345194894533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18720823267760896796596355 28081234901641345194894533)
                ·
                  refine ⟨5265231544057752224042725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28081234901641345194894533 5265231544057752224042725)
                  ·
                    refine ⟨987230914510828542008011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5265231544057752224042725 987230914510828542008011)
                    ·
                      rfl

theorem cell22_2883938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2883938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883938 prefixEnd_2883938 := by exact prefixLift 2883938
  have htrace : WordTrace (prefixWord ++ tailWord_2883938) baseStart_2883938 baseEnd_2883938 := by
    simpa [prefixWord, tailWord_2883938, baseEnd_2883938] using wordTrace_append hprefix tailTrace_2883938
  have hstable : (prefixWord ++ tailWord_2883938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883938).length < 2 ^ (prefixWord ++ tailWord_2883938).sum := by decide
  have hdescent : baseEnd_2883938 < baseStart_2883938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2883957 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 2, 3]
def baseStart_2883957 : Nat := 118140960795 + 2883957 * 2 ^ 59
def prefixEnd_2883957 : Nat := 4983230072969 + 3 ^ 40 * 2883957 * 2
def baseEnd_2883957 : Nat := 987237418599118825782953

theorem tailTrace_2883957 : CollatzResearch.WordTrace tailWord_2883957 prefixEnd_2883957 987237418599118825782953 := by
  unfold tailWord_2883957
  simp only [CollatzResearch.WordTrace]
  refine ⟨105186553212923804487546125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70124368808615869658364083 105186553212923804487546125)
  ·
    refine ⟨39444957454846426682829797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105186553212923804487546125 39444957454846426682829797)
    ·
      refine ⟨7395929522783705003030587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39444957454846426682829797 7395929522783705003030587)
      ·
        refine ⟨11093894284175557504545881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7395929522783705003030587 11093894284175557504545881)
        ·
          refine ⟨8320420713131668128409411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11093894284175557504545881 8320420713131668128409411)
          ·
            refine ⟨12480631069697502192614117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8320420713131668128409411 12480631069697502192614117)
            ·
              refine ⟨2340118325568281661115147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12480631069697502192614117 2340118325568281661115147)
              ·
                refine ⟨3510177488352422491672721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340118325568281661115147 3510177488352422491672721)
                ·
                  refine ⟨2632633116264316868754541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3510177488352422491672721 2632633116264316868754541)
                  ·
                    refine ⟨987237418599118825782953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632633116264316868754541 987237418599118825782953)
                    ·
                      rfl

theorem cell22_2883957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 2, 3].length) (baseStart_2883957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2883957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2883957 prefixEnd_2883957 := by exact prefixLift 2883957
  have htrace : WordTrace (prefixWord ++ tailWord_2883957) baseStart_2883957 baseEnd_2883957 := by
    simpa [prefixWord, tailWord_2883957, baseEnd_2883957] using wordTrace_append hprefix tailTrace_2883957
  have hstable : (prefixWord ++ tailWord_2883957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2883957).length < 2 ^ (prefixWord ++ tailWord_2883957).sum := by decide
  have hdescent : baseEnd_2883957 < baseStart_2883957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2883957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884002 : List Nat := [3, 3, 1, 2, 1, 1, 3, 4, 1, 3]
def baseStart_2884002 : Nat := 118140960795 + 2884002 * 2 ^ 59
def prefixEnd_2884002 : Nat := 4983230072969 + 3 ^ 40 * 2884002 * 2
def baseEnd_2884002 : Nat := 987252823018753708407815

theorem tailTrace_2884002 : CollatzResearch.WordTrace tailWord_2884002 prefixEnd_2884002 987252823018753708407815 := by
  unfold tailWord_2884002
  simp only [CollatzResearch.WordTrace]
  refine ⟨26297048624440194293233565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70125462998507184781956173 26297048624440194293233565)
  ·
    refine ⟨9861393234165072859962587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26297048624440194293233565 9861393234165072859962587)
    ·
      refine ⟨14792089851247609289943881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9861393234165072859962587 14792089851247609289943881)
      ·
        refine ⟨11094067388435706967457911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14792089851247609289943881 11094067388435706967457911)
        ·
          refine ⟨16641101082653560451186867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11094067388435706967457911 16641101082653560451186867)
          ·
            refine ⟨24961651623980340676780301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16641101082653560451186867 24961651623980340676780301)
            ·
              refine ⟨9360619358992627753792613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24961651623980340676780301 9360619358992627753792613)
              ·
                refine ⟨1755116129811117703836115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9360619358992627753792613 1755116129811117703836115)
                ·
                  refine ⟨2632674194716676555754173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755116129811117703836115 2632674194716676555754173)
                  ·
                    refine ⟨987252823018753708407815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632674194716676555754173 987252823018753708407815)
                    ·
                      rfl

theorem cell22_2884002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 1, 3].length) (baseStart_2884002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884002 prefixEnd_2884002 := by exact prefixLift 2884002
  have htrace : WordTrace (prefixWord ++ tailWord_2884002) baseStart_2884002 baseEnd_2884002 := by
    simpa [prefixWord, tailWord_2884002, baseEnd_2884002] using wordTrace_append hprefix tailTrace_2884002
  have hstable : (prefixWord ++ tailWord_2884002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884002).length < 2 ^ (prefixWord ++ tailWord_2884002).sum := by decide
  have hdescent : baseEnd_2884002 < baseStart_2884002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884109 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_2884109 : Nat := 118140960795 + 2884109 * 2 ^ 59
def prefixEnd_2884109 : Nat := 4983230072969 + 3 ^ 40 * 2884109 * 2
def baseEnd_2884109 : Nat := 987289451305441095982487

theorem tailTrace_2884109 : CollatzResearch.WordTrace tailWord_2884109 prefixEnd_2884109 987289451305441095982487 := by
  unfold tailWord_2884109
  simp only [CollatzResearch.WordTrace]
  refine ⟨105192097108373134447079381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70128064738915422964719587 105192097108373134447079381)
  ·
    refine ⟨2465439775977495338603423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 105192097108373134447079381 2465439775977495338603423)
    ·
      refine ⟨3698159663966243007905135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2465439775977495338603423 3698159663966243007905135)
      ·
        refine ⟨5547239495949364511857703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3698159663966243007905135 5547239495949364511857703)
        ·
          refine ⟨8320859243924046767786555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5547239495949364511857703 8320859243924046767786555)
          ·
            refine ⟨12481288865886070151679833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8320859243924046767786555 12481288865886070151679833)
            ·
              refine ⟨9360966649414552613759875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12481288865886070151679833 9360966649414552613759875)
              ·
                refine ⟨14041449974121828920639813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9360966649414552613759875 14041449974121828920639813)
                ·
                  refine ⟨2632771870147842922619965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14041449974121828920639813 2632771870147842922619965)
                  ·
                    refine ⟨987289451305441095982487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632771870147842922619965 987289451305441095982487)
                    ·
                      rfl

theorem cell22_2884109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_2884109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884109 prefixEnd_2884109 := by exact prefixLift 2884109
  have htrace : WordTrace (prefixWord ++ tailWord_2884109) baseStart_2884109 baseEnd_2884109 := by
    simpa [prefixWord, tailWord_2884109, baseEnd_2884109] using wordTrace_append hprefix tailTrace_2884109
  have hstable : (prefixWord ++ tailWord_2884109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884109).length < 2 ^ (prefixWord ++ tailWord_2884109).sum := by decide
  have hdescent : baseEnd_2884109 < baseStart_2884109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884141 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_2884141 : Nat := 118140960795 + 2884141 * 2 ^ 59
def prefixEnd_2884141 : Nat := 4983230072969 + 3 ^ 40 * 2884141 * 2
def baseEnd_2884141 : Nat := 987300405559403679182389

theorem tailTrace_2884141 : CollatzResearch.WordTrace tailWord_2884141 prefixEnd_2884141 987300405559403679182389 := by
  unfold tailWord_2884141
  simp only [CollatzResearch.WordTrace]
  refine ⟨105193264244257203912244277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70128842829504802608162851 105193264244257203912244277)
  ·
    refine ⟨9861868522899112866772901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105193264244257203912244277 9861868522899112866772901)
    ·
      refine ⟨1849100348043583662519919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9861868522899112866772901 1849100348043583662519919)
      ·
        refine ⟨2773650522065375493779879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849100348043583662519919 2773650522065375493779879)
        ·
          refine ⟨4160475783098063240669819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2773650522065375493779879 4160475783098063240669819)
          ·
            refine ⟨6240713674647094861004729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160475783098063240669819 6240713674647094861004729)
            ·
              refine ⟨4680535255985321145753547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6240713674647094861004729 4680535255985321145753547)
              ·
                refine ⟨7020802883977981718630321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680535255985321145753547 7020802883977981718630321)
                ·
                  refine ⟨5265602162983486288972741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7020802883977981718630321 5265602162983486288972741)
                  ·
                    refine ⟨987300405559403679182389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5265602162983486288972741 987300405559403679182389)
                    ·
                      rfl

theorem cell22_2884141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_2884141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884141 prefixEnd_2884141 := by exact prefixLift 2884141
  have htrace : WordTrace (prefixWord ++ tailWord_2884141) baseStart_2884141 baseEnd_2884141 := by
    simpa [prefixWord, tailWord_2884141, baseEnd_2884141] using wordTrace_append hprefix tailTrace_2884141
  have hstable : (prefixWord ++ tailWord_2884141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884141).length < 2 ^ (prefixWord ++ tailWord_2884141).sum := by decide
  have hdescent : baseEnd_2884141 < baseStart_2884141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884180 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 3, 4]
def baseStart_2884180 : Nat := 118140960795 + 2884180 * 2 ^ 59
def prefixEnd_2884180 : Nat := 4983230072969 + 3 ^ 40 * 2884180 * 2
def baseEnd_2884180 : Nat := 987313756056420577457269

theorem tailTrace_2884180 : CollatzResearch.WordTrace tailWord_2884180 prefixEnd_2884180 987313756056420577457269 := by
  unfold tailWord_2884180
  simp only [CollatzResearch.WordTrace]
  refine ⟨52597343345557956786456997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70129791127410609048609329 52597343345557956786456997)
  ·
    refine ⟨9862001877292116897460687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52597343345557956786456997 9862001877292116897460687)
    ·
      refine ⟨14793002815938175346191031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9862001877292116897460687 14793002815938175346191031)
      ·
        refine ⟨22189504223907263019286547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14793002815938175346191031 22189504223907263019286547)
        ·
          refine ⟨33284256335860894528929821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22189504223907263019286547 33284256335860894528929821)
          ·
            refine ⟨12481596125947835448348683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33284256335860894528929821 12481596125947835448348683)
            ·
              refine ⟨18722394188921753172523025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12481596125947835448348683 18722394188921753172523025)
              ·
                refine ⟨14041795641691314879392269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18722394188921753172523025 14041795641691314879392269)
                ·
                  refine ⟨5265673365634243079772101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14041795641691314879392269 5265673365634243079772101)
                  ·
                    refine ⟨987313756056420577457269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5265673365634243079772101 987313756056420577457269)
                    ·
                      rfl

theorem cell22_2884180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 3, 4].length) (baseStart_2884180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884180 prefixEnd_2884180 := by exact prefixLift 2884180
  have htrace : WordTrace (prefixWord ++ tailWord_2884180) baseStart_2884180 baseEnd_2884180 := by
    simpa [prefixWord, tailWord_2884180, baseEnd_2884180] using wordTrace_append hprefix tailTrace_2884180
  have hstable : (prefixWord ++ tailWord_2884180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884180).length < 2 ^ (prefixWord ++ tailWord_2884180).sum := by decide
  have hdescent : baseEnd_2884180 < baseStart_2884180 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884214 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_2884214 : Nat := 118140960795 + 2884214 * 2 ^ 59
def prefixEnd_2884214 : Nat := 4983230072969 + 3 ^ 40 * 2884214 * 2
def baseEnd_2884214 : Nat := 987325394951255822107165

theorem tailTrace_2884214 : CollatzResearch.WordTrace tailWord_2884214 prefixEnd_2884214 987325394951255822107165 := by
  unfold tailWord_2884214
  simp only [CollatzResearch.WordTrace]
  refine ⟨6574745423312046086228231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 70130617848661824919767797 6574745423312046086228231)
  ·
    refine ⟨9862118134968069129342347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6574745423312046086228231 9862118134968069129342347)
    ·
      refine ⟨14793177202452103694013521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9862118134968069129342347 14793177202452103694013521)
      ·
        refine ⟨11094882901839077770510141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14793177202452103694013521 11094882901839077770510141)
        ·
          refine ⟨4160581088189654163941303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11094882901839077770510141 4160581088189654163941303)
          ·
            refine ⟨6240871632284481245911955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160581088189654163941303 6240871632284481245911955)
            ·
              refine ⟨9361307448426721868867933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6240871632284481245911955 9361307448426721868867933)
              ·
                refine ⟨3510490293160020700825475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9361307448426721868867933 3510490293160020700825475)
                ·
                  refine ⟨5265735439740031051238213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510490293160020700825475 5265735439740031051238213)
                  ·
                    refine ⟨987325394951255822107165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5265735439740031051238213 987325394951255822107165)
                    ·
                      rfl

theorem cell22_2884214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_2884214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884214 prefixEnd_2884214 := by exact prefixLift 2884214
  have htrace : WordTrace (prefixWord ++ tailWord_2884214) baseStart_2884214 baseEnd_2884214 := by
    simpa [prefixWord, tailWord_2884214, baseEnd_2884214] using wordTrace_append hprefix tailTrace_2884214
  have hstable : (prefixWord ++ tailWord_2884214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884214).length < 2 ^ (prefixWord ++ tailWord_2884214).sum := by decide
  have hdescent : baseEnd_2884214 < baseStart_2884214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884225 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 4, 4]
def baseStart_2884225 : Nat := 118140960795 + 2884225 * 2 ^ 59
def prefixEnd_2884225 : Nat := 4983230072969 + 3 ^ 40 * 2884225 * 2
def baseEnd_2884225 : Nat := 987329160476055460082131

theorem tailTrace_2884225 : CollatzResearch.WordTrace tailWord_2884225 prefixEnd_2884225 987329160476055460082131 := by
  unfold tailWord_2884225
  simp only [CollatzResearch.WordTrace]
  refine ⟨105196327975952886258302129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70130885317301924172201419 105196327975952886258302129)
  ·
    refine ⟨78897245981964664693726597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105196327975952886258302129 78897245981964664693726597)
    ·
      refine ⟨14793233621618374630073737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78897245981964664693726597 14793233621618374630073737)
      ·
        refine ⟨11094925216213780972555303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14793233621618374630073737 11094925216213780972555303)
        ·
          refine ⟨16642387824320671458832955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11094925216213780972555303 16642387824320671458832955)
          ·
            refine ⟨24963581736481007188249433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16642387824320671458832955 24963581736481007188249433)
            ·
              refine ⟨18722686302360755391187075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24963581736481007188249433 18722686302360755391187075)
              ·
                refine ⟨28084029453541133086780613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18722686302360755391187075 28084029453541133086780613)
                ·
                  refine ⟨5265755522538962453771365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28084029453541133086780613 5265755522538962453771365)
                  ·
                    refine ⟨987329160476055460082131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5265755522538962453771365 987329160476055460082131)
                    ·
                      rfl

theorem cell22_2884225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_2884225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884225 prefixEnd_2884225 := by exact prefixLift 2884225
  have htrace : WordTrace (prefixWord ++ tailWord_2884225) baseStart_2884225 baseEnd_2884225 := by
    simpa [prefixWord, tailWord_2884225, baseEnd_2884225] using wordTrace_append hprefix tailTrace_2884225
  have hstable : (prefixWord ++ tailWord_2884225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884225).length < 2 ^ (prefixWord ++ tailWord_2884225).sum := by decide
  have hdescent : baseEnd_2884225 < baseStart_2884225 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884227 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 2, 3]
def baseStart_2884227 : Nat := 118140960795 + 2884227 * 2 ^ 59
def prefixEnd_2884227 : Nat := 4983230072969 + 3 ^ 40 * 2884227 * 2
def baseEnd_2884227 : Nat := 987329845116928121532125

theorem tailTrace_2884227 : CollatzResearch.WordTrace tailWord_2884227 prefixEnd_2884227 987329845116928121532125 := by
  unfold tailWord_2884227
  simp only [CollatzResearch.WordTrace]
  refine ⟨105196400921945640599874935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70130933947963760399916623 105196400921945640599874935)
  ·
    refine ⟨157794601382918460899812403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105196400921945640599874935 157794601382918460899812403)
    ·
      refine ⟨236691902074377691349718605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157794601382918460899812403 236691902074377691349718605)
      ·
        refine ⟨88759463277891634256144477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236691902074377691349718605 88759463277891634256144477)
        ·
          refine ⟨33284798729209362846054179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88759463277891634256144477 33284798729209362846054179)
          ·
            refine ⟨49927198093814044269081269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33284798729209362846054179 49927198093814044269081269)
            ·
              refine ⟨4680674821295066650226369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 49927198093814044269081269 4680674821295066650226369)
              ·
                refine ⟨3510506115971299987669777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4680674821295066650226369 3510506115971299987669777)
                ·
                  refine ⟨2632879586978474990752333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3510506115971299987669777 2632879586978474990752333)
                  ·
                    refine ⟨987329845116928121532125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632879586978474990752333 987329845116928121532125)
                    ·
                      rfl

theorem cell22_2884227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 2, 3].length) (baseStart_2884227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884227 prefixEnd_2884227 := by exact prefixLift 2884227
  have htrace : WordTrace (prefixWord ++ tailWord_2884227) baseStart_2884227 baseEnd_2884227 := by
    simpa [prefixWord, tailWord_2884227, baseEnd_2884227] using wordTrace_append hprefix tailTrace_2884227
  have hstable : (prefixWord ++ tailWord_2884227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884227).length < 2 ^ (prefixWord ++ tailWord_2884227).sum := by decide
  have hdescent : baseEnd_2884227 < baseStart_2884227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884244 : List Nat := [2, 4, 2, 2, 1, 3, 1, 1, 1, 5]
def baseStart_2884244 : Nat := 118140960795 + 2884244 * 2 ^ 59
def prefixEnd_2884244 : Nat := 4983230072969 + 3 ^ 40 * 2884244 * 2
def baseEnd_2884244 : Nat := 987335664564345743857073

theorem tailTrace_2884244 : CollatzResearch.WordTrace tailWord_2884244 prefixEnd_2884244 987335664564345743857073 := by
  unfold tailWord_2884244
  simp only [CollatzResearch.WordTrace]
  refine ⟨52598510481442026251621893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70131347308589368335495857 52598510481442026251621893)
  ·
    refine ⟨9862220715270379922179105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 52598510481442026251621893 9862220715270379922179105)
    ·
      refine ⟨7396665536452784941634329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9862220715270379922179105 7396665536452784941634329)
      ·
        refine ⟨5547499152339588706225747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7396665536452784941634329 5547499152339588706225747)
        ·
          refine ⟨8321248728509383059338621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5547499152339588706225747 8321248728509383059338621)
          ·
            refine ⟨3120468273191018647251983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8321248728509383059338621 3120468273191018647251983)
            ·
              refine ⟨4680702409786527970877975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120468273191018647251983 4680702409786527970877975)
              ·
                refine ⟨7021053614679791956316963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680702409786527970877975 7021053614679791956316963)
                ·
                  refine ⟨10531580422019687934475445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7021053614679791956316963 10531580422019687934475445)
                  ·
                    refine ⟨987335664564345743857073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10531580422019687934475445 987335664564345743857073)
                    ·
                      rfl

theorem cell22_2884244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 3, 1, 1, 1, 5].length) (baseStart_2884244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884244 prefixEnd_2884244 := by exact prefixLift 2884244
  have htrace : WordTrace (prefixWord ++ tailWord_2884244) baseStart_2884244 baseEnd_2884244 := by
    simpa [prefixWord, tailWord_2884244, baseEnd_2884244] using wordTrace_append hprefix tailTrace_2884244
  have hstable : (prefixWord ++ tailWord_2884244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884244).length < 2 ^ (prefixWord ++ tailWord_2884244).sum := by decide
  have hdescent : baseEnd_2884244 < baseStart_2884244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884263 : List Nat := [1, 1, 6, 3, 2, 1, 1, 3, 4]
def baseStart_2884263 : Nat := 118140960795 + 2884263 * 2 ^ 59
def prefixEnd_2884263 : Nat := 4983230072969 + 3 ^ 40 * 2884263 * 2
def baseEnd_2884263 : Nat := 329114056217545342544005

theorem tailTrace_2884263 : CollatzResearch.WordTrace tailWord_2884263 prefixEnd_2884263 329114056217545342544005 := by
  unfold tailWord_2884263
  simp only [CollatzResearch.WordTrace]
  refine ⟨105197713949815218748185443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70131809299876812498790295 105197713949815218748185443)
  ·
    refine ⟨157796570924722828122278165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105197713949815218748185443 157796570924722828122278165)
    ·
      refine ⟨7396714262096382568231789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 157796570924722828122278165 7396714262096382568231789)
      ·
        refine ⟨2773767848286143463086921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7396714262096382568231789 2773767848286143463086921)
        ·
          refine ⟨2080325886214607597315191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2773767848286143463086921 2080325886214607597315191)
          ·
            refine ⟨3120488829321911395972787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080325886214607597315191 3120488829321911395972787)
            ·
              refine ⟨4680733243982867093959181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120488829321911395972787 4680733243982867093959181)
              ·
                refine ⟨1755274966493575160234693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4680733243982867093959181 1755274966493575160234693)
                ·
                  refine ⟨329114056217545342544005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1755274966493575160234693 329114056217545342544005)
                  ·
                    rfl

theorem cell22_2884263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 3, 4].length) (baseStart_2884263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884263 prefixEnd_2884263 := by exact prefixLift 2884263
  have htrace : WordTrace (prefixWord ++ tailWord_2884263) baseStart_2884263 baseEnd_2884263 := by
    simpa [prefixWord, tailWord_2884263, baseEnd_2884263] using wordTrace_append hprefix tailTrace_2884263
  have hstable : (prefixWord ++ tailWord_2884263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884263).length < 2 ^ (prefixWord ++ tailWord_2884263).sum := by decide
  have hdescent : baseEnd_2884263 < baseStart_2884263 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884285 : List Nat := [1, 4, 1, 2, 1, 3, 2, 1, 7]
def baseStart_2884285 : Nat := 118140960795 + 2884285 * 2 ^ 59
def prefixEnd_2884285 : Nat := 4983230072969 + 3 ^ 40 * 2884285 * 2
def baseEnd_2884285 : Nat := 329116566567411767860649

theorem tailTrace_2884285 : CollatzResearch.WordTrace tailWord_2884285 prefixEnd_2884285 329116566567411767860649 := by
  unfold tailWord_2884285
  simp only [CollatzResearch.WordTrace]
  refine ⟨105198516355735516505486309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70132344237157011003657539 105198516355735516505486309)
  ·
    refine ⟨19724721816700409344778683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105198516355735516505486309 19724721816700409344778683)
    ·
      refine ⟨29587082725050614017168025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19724721816700409344778683 29587082725050614017168025)
      ·
        refine ⟨22190312043787960512876019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29587082725050614017168025 22190312043787960512876019)
        ·
          refine ⟨33285468065681940769314029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22190312043787960512876019 33285468065681940769314029)
          ·
            refine ⟨12482050524630727788492761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33285468065681940769314029 12482050524630727788492761)
            ·
              refine ⟨9361537893473045841369571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12482050524630727788492761 9361537893473045841369571)
              ·
                refine ⟨14042306840209568762054357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9361537893473045841369571 14042306840209568762054357)
                ·
                  refine ⟨329116566567411767860649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14042306840209568762054357 329116566567411767860649)
                  ·
                    rfl

theorem cell22_2884285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 2, 1, 7].length) (baseStart_2884285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884285 prefixEnd_2884285 := by exact prefixLift 2884285
  have htrace : WordTrace (prefixWord ++ tailWord_2884285) baseStart_2884285 baseEnd_2884285 := by
    simpa [prefixWord, tailWord_2884285, baseEnd_2884285] using wordTrace_append hprefix tailTrace_2884285
  have hstable : (prefixWord ++ tailWord_2884285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884285).length < 2 ^ (prefixWord ++ tailWord_2884285).sum := by decide
  have hdescent : baseEnd_2884285 < baseStart_2884285 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884302 : List Nat := [4, 1, 1, 1, 3, 3, 1, 3, 5]
def baseStart_2884302 : Nat := 118140960795 + 2884302 * 2 ^ 59
def prefixEnd_2884302 : Nat := 4983230072969 + 3 ^ 40 * 2884302 * 2
def baseEnd_2884302 : Nat := 329118506383217641968965

theorem tailTrace_2884302 : CollatzResearch.WordTrace tailWord_2884302 prefixEnd_2884302 329118506383217641968965 := by
  unfold tailWord_2884302
  simp only [CollatzResearch.WordTrace]
  refine ⟨13149892049584241051106895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70132757597782618939236773 13149892049584241051106895)
  ·
    refine ⟨19724838074376361576660343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13149892049584241051106895 19724838074376361576660343)
    ·
      refine ⟨29587257111564542364990515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19724838074376361576660343 29587257111564542364990515)
      ·
        refine ⟨44380885667346813547485773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29587257111564542364990515 44380885667346813547485773)
        ·
          refine ⟨16642832125255055080307165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44380885667346813547485773 16642832125255055080307165)
          ·
            refine ⟨6241062046970645655115187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16642832125255055080307165 6241062046970645655115187)
            ·
              refine ⟨9361593070455968482672781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6241062046970645655115187 9361593070455968482672781)
              ·
                refine ⟨3510597401420988181002293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9361593070455968482672781 3510597401420988181002293)
                ·
                  refine ⟨329118506383217641968965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3510597401420988181002293 329118506383217641968965)
                  ·
                    rfl

theorem cell22_2884302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 1, 3, 5].length) (baseStart_2884302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884302 prefixEnd_2884302 := by exact prefixLift 2884302
  have htrace : WordTrace (prefixWord ++ tailWord_2884302) baseStart_2884302 baseEnd_2884302 := by
    simpa [prefixWord, tailWord_2884302, baseEnd_2884302] using wordTrace_append hprefix tailTrace_2884302
  have hstable : (prefixWord ++ tailWord_2884302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884302).length < 2 ^ (prefixWord ++ tailWord_2884302).sum := by decide
  have hdescent : baseEnd_2884302 < baseStart_2884302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884340 : List Nat := [2, 6, 1, 1, 2, 1, 1, 4, 1, 3]
def baseStart_2884340 : Nat := 118140960795 + 2884340 * 2 ^ 59
def prefixEnd_2884340 : Nat := 4983230072969 + 3 ^ 40 * 2884340 * 2
def baseEnd_2884340 : Nat := 987368527326233493456779

theorem tailTrace_2884340 : CollatzResearch.WordTrace tailWord_2884340 prefixEnd_2884340 987368527326233493456779 := by
  unfold tailWord_2884340
  simp only [CollatzResearch.WordTrace]
  refine ⟨52600261185268130449369237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70133681580357507265825649 52600261185268130449369237)
  ·
    refine ⟨2465637243059443614814183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52600261185268130449369237 2465637243059443614814183)
    ·
      refine ⟨3698455864589165422221275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2465637243059443614814183 3698455864589165422221275)
      ·
        refine ⟨5547683796883748133331913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3698455864589165422221275 5547683796883748133331913)
        ·
          refine ⟨4160762847662811099998935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5547683796883748133331913 4160762847662811099998935)
          ·
            refine ⟨6241144271494216649998403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160762847662811099998935 6241144271494216649998403)
            ·
              refine ⟨9361716407241324974997605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6241144271494216649998403 9361716407241324974997605)
              ·
                refine ⟨1755321826357748432812051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9361716407241324974997605 1755321826357748432812051)
                ·
                  refine ⟨2632982739536622649218077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755321826357748432812051 2632982739536622649218077)
                  ·
                    refine ⟨987368527326233493456779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2632982739536622649218077 987368527326233493456779)
                    ·
                      rfl

theorem cell22_2884340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_2884340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884340 prefixEnd_2884340 := by exact prefixLift 2884340
  have htrace : WordTrace (prefixWord ++ tailWord_2884340) baseStart_2884340 baseEnd_2884340 := by
    simpa [prefixWord, tailWord_2884340, baseEnd_2884340] using wordTrace_append hprefix tailTrace_2884340
  have hstable : (prefixWord ++ tailWord_2884340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884340).length < 2 ^ (prefixWord ++ tailWord_2884340).sum := by decide
  have hdescent : baseEnd_2884340 < baseStart_2884340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884362 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 1, 5]
def baseStart_2884362 : Nat := 118140960795 + 2884362 * 2 ^ 59
def prefixEnd_2884362 : Nat := 4983230072969 + 3 ^ 40 * 2884362 * 2
def baseEnd_2884362 : Nat := 987376058375832769406711

theorem tailTrace_2884362 : CollatzResearch.WordTrace tailWord_2884362 prefixEnd_2884362 987376058375832769406711 := by
  unfold tailWord_2884362
  simp only [CollatzResearch.WordTrace]
  refine ⟨26300331194114139664009835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70134216517637705770692893 26300331194114139664009835)
  ·
    refine ⟨39450496791171209496014753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26300331194114139664009835 39450496791171209496014753)
    ·
      refine ⟨29587872593378407122011065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39450496791171209496014753 29587872593378407122011065)
      ·
        refine ⟨22190904445033805341508299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29587872593378407122011065 22190904445033805341508299)
        ·
          refine ⟨33286356667550708012262449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22190904445033805341508299 33286356667550708012262449)
          ·
            refine ⟨24964767500663031009196837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33286356667550708012262449 24964767500663031009196837)
            ·
              refine ⟨4680893906374318314224407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24964767500663031009196837 4680893906374318314224407)
              ·
                refine ⟨7021340859561477471336611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4680893906374318314224407 7021340859561477471336611)
                ·
                  refine ⟨10532011289342216207004917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7021340859561477471336611 10532011289342216207004917)
                  ·
                    refine ⟨987376058375832769406711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10532011289342216207004917 987376058375832769406711)
                    ·
                      rfl

theorem cell22_2884362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 5].length) (baseStart_2884362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884362 prefixEnd_2884362 := by exact prefixLift 2884362
  have htrace : WordTrace (prefixWord ++ tailWord_2884362) baseStart_2884362 baseEnd_2884362 := by
    simpa [prefixWord, tailWord_2884362, baseEnd_2884362] using wordTrace_append hprefix tailTrace_2884362
  have hstable : (prefixWord ++ tailWord_2884362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884362).length < 2 ^ (prefixWord ++ tailWord_2884362).sum := by decide
  have hdescent : baseEnd_2884362 < baseStart_2884362 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884413 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 2, 3]
def baseStart_2884413 : Nat := 118140960795 + 2884413 * 2 ^ 59
def prefixEnd_2884413 : Nat := 4983230072969 + 3 ^ 40 * 2884413 * 2
def baseEnd_2884413 : Nat := 987393516718085636381555

theorem tailTrace_2884413 : CollatzResearch.WordTrace tailWord_2884413 prefixEnd_2884413 987393516718085636381555 := by
  unfold tailWord_2884413
  simp only [CollatzResearch.WordTrace]
  refine ⟨105203184899271794366145893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70135456599514529577430595 105203184899271794366145893)
  ·
    refine ⟨19725597168613461443652355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105203184899271794366145893 19725597168613461443652355)
    ·
      refine ⟨29588395752920192165478533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19725597168613461443652355 29588395752920192165478533)
      ·
        refine ⟨5547824203672536031027225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29588395752920192165478533 5547824203672536031027225)
        ·
          refine ⟨4160868152754402023270419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5547824203672536031027225 4160868152754402023270419)
          ·
            refine ⟨6241302229131603034905629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4160868152754402023270419 6241302229131603034905629)
            ·
              refine ⟨2340488335924351138089611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6241302229131603034905629 2340488335924351138089611)
              ·
                refine ⟨3510732503886526707134417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340488335924351138089611 3510732503886526707134417)
                ·
                  refine ⟨2633049377914895030350813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3510732503886526707134417 2633049377914895030350813)
                  ·
                    refine ⟨987393516718085636381555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2633049377914895030350813 987393516718085636381555)
                    ·
                      rfl

theorem cell22_2884413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 2, 3].length) (baseStart_2884413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884413 prefixEnd_2884413 := by exact prefixLift 2884413
  have htrace : WordTrace (prefixWord ++ tailWord_2884413) baseStart_2884413 baseEnd_2884413 := by
    simpa [prefixWord, tailWord_2884413, baseEnd_2884413] using wordTrace_append hprefix tailTrace_2884413
  have hstable : (prefixWord ++ tailWord_2884413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884413).length < 2 ^ (prefixWord ++ tailWord_2884413).sum := by decide
  have hdescent : baseEnd_2884413 < baseStart_2884413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884435 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 1, 7]
def baseStart_2884435 : Nat := 118140960795 + 2884435 * 2 ^ 59
def prefixEnd_2884435 : Nat := 4983230072969 + 3 ^ 40 * 2884435 * 2
def baseEnd_2884435 : Nat := 987401047767684912331487

theorem tailTrace_2884435 : CollatzResearch.WordTrace tailWord_2884435 prefixEnd_2884435 987401047767684912331487 := by
  unfold tailWord_2884435
  simp only [CollatzResearch.WordTrace]
  refine ⟨105203987305192092123446759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70135991536794728082297839 105203987305192092123446759)
  ·
    refine ⟨157805980957788138185170139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105203987305192092123446759 157805980957788138185170139)
    ·
      refine ⟨236708971436682207277755209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157805980957788138185170139 236708971436682207277755209)
      ·
        refine ⟨177531728577511655458316407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236708971436682207277755209 177531728577511655458316407)
        ·
          refine ⟨266297592866267483187474611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177531728577511655458316407 266297592866267483187474611)
          ·
            refine ⟨399446389299401224781211917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266297592866267483187474611 399446389299401224781211917)
            ·
              refine ⟨149792395987275459292954469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 399446389299401224781211917 149792395987275459292954469)
              ·
                refine ⟨28086074247614148617428963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149792395987275459292954469 28086074247614148617428963)
                ·
                  refine ⟨42129111371421222926143445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28086074247614148617428963 42129111371421222926143445)
                  ·
                    refine ⟨987401047767684912331487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42129111371421222926143445 987401047767684912331487)
                    ·
                      rfl

theorem cell22_2884435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 7].length) (baseStart_2884435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884435 prefixEnd_2884435 := by exact prefixLift 2884435
  have htrace : WordTrace (prefixWord ++ tailWord_2884435) baseStart_2884435 baseEnd_2884435 := by
    simpa [prefixWord, tailWord_2884435, baseEnd_2884435] using wordTrace_append hprefix tailTrace_2884435
  have hstable : (prefixWord ++ tailWord_2884435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884435).length < 2 ^ (prefixWord ++ tailWord_2884435).sum := by decide
  have hdescent : baseEnd_2884435 < baseStart_2884435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884441 : List Nat := [1, 2, 1, 2, 2, 4, 3, 3, 1, 3]
def baseStart_2884441 : Nat := 118140960795 + 2884441 * 2 ^ 59
def prefixEnd_2884441 : Nat := 4983230072969 + 3 ^ 40 * 2884441 * 2
def baseEnd_2884441 : Nat := 987403101690302896681469

theorem tailTrace_2884441 : CollatzResearch.WordTrace tailWord_2884441 prefixEnd_2884441 987403101690302896681469 := by
  unfold tailWord_2884441
  simp only [CollatzResearch.WordTrace]
  refine ⟨105204206143170355148165177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70136137428780236765443451 105204206143170355148165177)
  ·
    refine ⟨78903154607377766361123883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105204206143170355148165177 78903154607377766361123883)
    ·
      refine ⟨118354731911066649541685825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78903154607377766361123883 118354731911066649541685825)
      ·
        refine ⟨88766048933299987156264369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118354731911066649541685825 88766048933299987156264369)
        ·
          refine ⟨66574536699974990367198277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88766048933299987156264369 66574536699974990367198277)
          ·
            refine ⟨12482725631245310693849677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66574536699974990367198277 12482725631245310693849677)
            ·
              refine ⟨4681022111716991510193629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12482725631245310693849677 4681022111716991510193629)
              ·
                refine ⟨1755383291893871816322611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4681022111716991510193629 1755383291893871816322611)
                ·
                  refine ⟨2633074937840807724483917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755383291893871816322611 2633074937840807724483917)
                  ·
                    refine ⟨987403101690302896681469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2633074937840807724483917 987403101690302896681469)
                    ·
                      rfl

theorem cell22_2884441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 1, 3].length) (baseStart_2884441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884441 prefixEnd_2884441 := by exact prefixLift 2884441
  have htrace : WordTrace (prefixWord ++ tailWord_2884441) baseStart_2884441 baseEnd_2884441 := by
    simpa [prefixWord, tailWord_2884441, baseEnd_2884441] using wordTrace_append hprefix tailTrace_2884441
  have hstable : (prefixWord ++ tailWord_2884441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884441).length < 2 ^ (prefixWord ++ tailWord_2884441).sum := by decide
  have hdescent : baseEnd_2884441 < baseStart_2884441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884501 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 1, 4]
def baseStart_2884501 : Nat := 118140960795 + 2884501 * 2 ^ 59
def prefixEnd_2884501 : Nat := 4983230072969 + 3 ^ 40 * 2884501 * 2
def baseEnd_2884501 : Nat := 987423640916482740181285

theorem tailTrace_2884501 : CollatzResearch.WordTrace tailWord_2884501 prefixEnd_2884501 987423640916482740181285 := by
  unfold tailWord_2884501
  simp only [CollatzResearch.WordTrace]
  refine ⟨105206394522952985395349357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70137596348635323596899571 105206394522952985395349357)
  ·
    refine ⟨39452397946107369523256009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105206394522952985395349357 39452397946107369523256009)
    ·
      refine ⟨29589298459580527142442007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39452397946107369523256009 29589298459580527142442007)
      ·
        refine ⟨44383947689370790713663011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29589298459580527142442007 44383947689370790713663011)
        ·
          refine ⟨66575921534056186070494517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44383947689370790713663011 66575921534056186070494517)
          ·
            refine ⟨6241492643817767444108861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66575921534056186070494517 6241492643817767444108861)
            ·
              refine ⟨2340559741431662791540823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6241492643817767444108861 2340559741431662791540823)
              ·
                refine ⟨3510839612147494187311235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340559741431662791540823 3510839612147494187311235)
                ·
                  refine ⟨5266259418221241280966853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3510839612147494187311235 5266259418221241280966853)
                  ·
                    refine ⟨987423640916482740181285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5266259418221241280966853 987423640916482740181285)
                    ·
                      rfl

theorem cell22_2884501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 1, 4].length) (baseStart_2884501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884501 prefixEnd_2884501 := by exact prefixLift 2884501
  have htrace : WordTrace (prefixWord ++ tailWord_2884501) baseStart_2884501 baseEnd_2884501 := by
    simpa [prefixWord, tailWord_2884501, baseEnd_2884501] using wordTrace_append hprefix tailTrace_2884501
  have hstable : (prefixWord ++ tailWord_2884501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884501).length < 2 ^ (prefixWord ++ tailWord_2884501).sum := by decide
  have hdescent : baseEnd_2884501 < baseStart_2884501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884544 : List Nat := [2, 1, 1, 2, 3, 4, 3, 6]
def baseStart_2884544 : Nat := 118140960795 + 2884544 * 2 ^ 59
def prefixEnd_2884544 : Nat := 4983230072969 + 3 ^ 40 * 2884544 * 2
def baseEnd_2884544 : Nat := 109715373410582773484017

theorem tailTrace_2884544 : CollatzResearch.WordTrace tailWord_2884544 prefixEnd_2884544 109715373410582773484017 := by
  unfold tailWord_2884544
  simp only [CollatzResearch.WordTrace]
  refine ⟨52603981430898601869582343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70138641907864802492776457 52603981430898601869582343)
  ·
    refine ⟨78905972146347902804373515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52603981430898601869582343 78905972146347902804373515)
    ·
      refine ⟨118358958219521854206560273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78905972146347902804373515 118358958219521854206560273)
      ·
        refine ⟨88769218664641390654920205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118358958219521854206560273 88769218664641390654920205)
        ·
          refine ⟨33288456999240521495595077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88769218664641390654920205 33288456999240521495595077)
          ·
            refine ⟨6241585687357597780424077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33288456999240521495595077 6241585687357597780424077)
            ·
              refine ⟨2340594632759099167659029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6241585687357597780424077 2340594632759099167659029)
              ·
                refine ⟨109715373410582773484017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2340594632759099167659029 109715373410582773484017)
                ·
                  rfl

theorem cell22_2884544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 6].length) (baseStart_2884544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884544 prefixEnd_2884544 := by exact prefixLift 2884544
  have htrace : WordTrace (prefixWord ++ tailWord_2884544) baseStart_2884544 baseEnd_2884544 := by
    simpa [prefixWord, tailWord_2884544, baseEnd_2884544] using wordTrace_append hprefix tailTrace_2884544
  have hstable : (prefixWord ++ tailWord_2884544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884544).length < 2 ^ (prefixWord ++ tailWord_2884544).sum := by decide
  have hdescent : baseEnd_2884544 < baseStart_2884544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884565 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 2, 3]
def baseStart_2884565 : Nat := 118140960795 + 2884565 * 2 ^ 59
def prefixEnd_2884565 : Nat := 4983230072969 + 3 ^ 40 * 2884565 * 2
def baseEnd_2884565 : Nat := 987445549424407906581089

theorem tailTrace_2884565 : CollatzResearch.WordTrace tailWord_2884565 prefixEnd_2884565 987445549424407906581089 := by
  unfold tailWord_2884565
  simp only [CollatzResearch.WordTrace]
  refine ⟨105208728794721124325679149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70139152529814082883786099 105208728794721124325679149)
  ·
    refine ⟨39453273298020421622129681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105208728794721124325679149 39453273298020421622129681)
    ·
      refine ⟨29589954973515316216597261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39453273298020421622129681 29589954973515316216597261)
      ·
        refine ⟨11096233115068243581223973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29589954973515316216597261 11096233115068243581223973)
        ·
          refine ⟨2080543709075295671479495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11096233115068243581223973 2080543709075295671479495)
          ·
            refine ⟨3120815563612943507219243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2080543709075295671479495 3120815563612943507219243)
            ·
              refine ⟨4681223345419415260828865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3120815563612943507219243 4681223345419415260828865)
              ·
                refine ⟨3510917509064561445621649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4681223345419415260828865 3510917509064561445621649)
                ·
                  refine ⟨2633188131798421084216237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3510917509064561445621649 2633188131798421084216237)
                  ·
                    refine ⟨987445549424407906581089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2633188131798421084216237 987445549424407906581089)
                    ·
                      rfl

theorem cell22_2884565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 2, 3].length) (baseStart_2884565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884565 prefixEnd_2884565 := by exact prefixLift 2884565
  have htrace : WordTrace (prefixWord ++ tailWord_2884565) baseStart_2884565 baseEnd_2884565 := by
    simpa [prefixWord, tailWord_2884565, baseEnd_2884565] using wordTrace_append hprefix tailTrace_2884565
  have hstable : (prefixWord ++ tailWord_2884565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884565).length < 2 ^ (prefixWord ++ tailWord_2884565).sum := by decide
  have hdescent : baseEnd_2884565 < baseStart_2884565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884602 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 2, 8]
def baseStart_2884602 : Nat := 118140960795 + 2884602 * 2 ^ 59
def prefixEnd_2884602 : Nat := 4983230072969 + 3 ^ 40 * 2884602 * 2
def baseEnd_2884602 : Nat := 987458215280552143405975

theorem tailTrace_2884602 : CollatzResearch.WordTrace tailWord_2884602 prefixEnd_2884602 987458215280552143405975 := by
  unfold tailWord_2884602
  simp only [CollatzResearch.WordTrace]
  refine ⟨26302519573896769911194015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70140052197058053096517373 26302519573896769911194015)
  ·
    refine ⟨39453779360845154866791023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26302519573896769911194015 39453779360845154866791023)
    ·
      refine ⟨59180669041267732300186535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39453779360845154866791023 59180669041267732300186535)
      ·
        refine ⟨88771003561901598450279803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59180669041267732300186535 88771003561901598450279803)
        ·
          refine ⟨133156505342852397675419705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88771003561901598450279803 133156505342852397675419705)
          ·
            refine ⟨99867379007139298256564779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133156505342852397675419705 99867379007139298256564779)
            ·
              refine ⟨149801068510708947384847169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99867379007139298256564779 149801068510708947384847169)
              ·
                refine ⟨112350801383031710538635377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149801068510708947384847169 112350801383031710538635377)
                ·
                  refine ⟨84263101037273782903976533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112350801383031710538635377 84263101037273782903976533)
                  ·
                    refine ⟨987458215280552143405975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84263101037273782903976533 987458215280552143405975)
                    ·
                      rfl

theorem cell22_2884602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 8].length) (baseStart_2884602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884602 prefixEnd_2884602 := by exact prefixLift 2884602
  have htrace : WordTrace (prefixWord ++ tailWord_2884602) baseStart_2884602 baseEnd_2884602 := by
    simpa [prefixWord, tailWord_2884602, baseEnd_2884602] using wordTrace_append hprefix tailTrace_2884602
  have hstable : (prefixWord ++ tailWord_2884602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884602).length < 2 ^ (prefixWord ++ tailWord_2884602).sum := by decide
  have hdescent : baseEnd_2884602 < baseStart_2884602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884617 : List Nat := [1, 2, 1, 1, 3, 1, 1, 4, 8]
def baseStart_2884617 : Nat := 118140960795 + 2884617 * 2 ^ 59
def prefixEnd_2884617 : Nat := 4983230072969 + 3 ^ 40 * 2884617 * 2
def baseEnd_2884617 : Nat := 329154450029032368093643

theorem tailTrace_2884617 : CollatzResearch.WordTrace tailWord_2884617 prefixEnd_2884617 329154450029032368093643 := by
  unfold tailWord_2884617
  simp only [CollatzResearch.WordTrace]
  refine ⟨105210625390532737206572105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70140416927021824804381403 105210625390532737206572105)
  ·
    refine ⟨78907969042899552904929079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105210625390532737206572105 78907969042899552904929079)
    ·
      refine ⟨118361953564349329357393619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78907969042899552904929079 118361953564349329357393619)
      ·
        refine ⟨177542930346523994036090429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118361953564349329357393619 177542930346523994036090429)
        ·
          refine ⟨66578598879946497763533911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177542930346523994036090429 66578598879946497763533911)
          ·
            refine ⟨99867898319919746645300867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66578598879946497763533911 99867898319919746645300867)
            ·
              refine ⟨149801847479879619967951301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99867898319919746645300867 149801847479879619967951301)
              ·
                refine ⟨28087846402477428743990869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149801847479879619967951301 28087846402477428743990869)
                ·
                  refine ⟨329154450029032368093643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28087846402477428743990869 329154450029032368093643)
                  ·
                    rfl

theorem cell22_2884617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 4, 8].length) (baseStart_2884617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884617 prefixEnd_2884617 := by exact prefixLift 2884617
  have htrace : WordTrace (prefixWord ++ tailWord_2884617) baseStart_2884617 baseEnd_2884617 := by
    simpa [prefixWord, tailWord_2884617, baseEnd_2884617] using wordTrace_append hprefix tailTrace_2884617
  have hstable : (prefixWord ++ tailWord_2884617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884617).length < 2 ^ (prefixWord ++ tailWord_2884617).sum := by decide
  have hdescent : baseEnd_2884617 < baseStart_2884617 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884640 : List Nat := [2, 1, 1, 7, 1, 2, 2, 1, 5]
def baseStart_2884640 : Nat := 118140960795 + 2884640 * 2 ^ 59
def prefixEnd_2884640 : Nat := 4983230072969 + 3 ^ 40 * 2884640 * 2
def baseEnd_2884640 : Nat := 329157074485710903651953

theorem tailTrace_2884640 : CollatzResearch.WordTrace tailWord_2884640 prefixEnd_2884640 329157074485710903651953 := by
  unfold tailWord_2884640
  simp only [CollatzResearch.WordTrace]
  refine ⟨52605732134724706067329687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70140976179632941423106249 52605732134724706067329687)
  ·
    refine ⟨78908598202087059100994531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52605732134724706067329687 78908598202087059100994531)
    ·
      refine ⟨118362897303130588651491797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78908598202087059100994531 118362897303130588651491797)
      ·
        refine ⟨2774130405542123171519339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 118362897303130588651491797 2774130405542123171519339)
        ·
          refine ⟨4161195608313184757279009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774130405542123171519339 4161195608313184757279009)
          ·
            refine ⟨3120896706234888567959257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4161195608313184757279009 3120896706234888567959257)
            ·
              refine ⟨2340672529676166425969443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3120896706234888567959257 2340672529676166425969443)
              ·
                refine ⟨3511008794514249638954165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340672529676166425969443 3511008794514249638954165)
                ·
                  refine ⟨329157074485710903651953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3511008794514249638954165 329157074485710903651953)
                  ·
                    rfl

theorem cell22_2884640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 2, 2, 1, 5].length) (baseStart_2884640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884640 prefixEnd_2884640 := by exact prefixLift 2884640
  have htrace : WordTrace (prefixWord ++ tailWord_2884640) baseStart_2884640 baseEnd_2884640 := by
    simpa [prefixWord, tailWord_2884640, baseEnd_2884640] using wordTrace_append hprefix tailTrace_2884640
  have hstable : (prefixWord ++ tailWord_2884640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884640).length < 2 ^ (prefixWord ++ tailWord_2884640).sum := by decide
  have hdescent : baseEnd_2884640 < baseStart_2884640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884670 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 1, 4]
def baseStart_2884670 : Nat := 118140960795 + 2884670 * 2 ^ 59
def prefixEnd_2884670 : Nat := 4983230072969 + 3 ^ 40 * 2884670 * 2
def baseEnd_2884670 : Nat := 987481493070222632705767

theorem tailTrace_2884670 : CollatzResearch.WordTrace tailWord_2884670 prefixEnd_2884670 987481493070222632705767 := by
  unfold tailWord_2884670
  simp only [CollatzResearch.WordTrace]
  refine ⟨13151569807417590907281433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70141705639560484838834309 13151569807417590907281433)
  ·
    refine ⟨9863677355563193180461075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13151569807417590907281433 9863677355563193180461075)
    ·
      refine ⟨14795516033344789770691613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9863677355563193180461075 14795516033344789770691613)
      ·
        refine ⟨5548318512504296164009355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14795516033344789770691613 5548318512504296164009355)
        ·
          refine ⟨8322477768756444246014033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5548318512504296164009355 8322477768756444246014033)
          ·
            refine ⟨6241858326567333184510525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8322477768756444246014033 6241858326567333184510525)
            ·
              refine ⟨2340696872462749944191447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6241858326567333184510525 2340696872462749944191447)
              ·
                refine ⟨3511045308694124916287171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2340696872462749944191447 3511045308694124916287171)
                ·
                  refine ⟨5266567963041187374430757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511045308694124916287171 5266567963041187374430757)
                  ·
                    refine ⟨987481493070222632705767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5266567963041187374430757 987481493070222632705767)
                    ·
                      rfl

theorem cell22_2884670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_2884670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884670 prefixEnd_2884670 := by exact prefixLift 2884670
  have htrace : WordTrace (prefixWord ++ tailWord_2884670) baseStart_2884670 baseEnd_2884670 := by
    simpa [prefixWord, tailWord_2884670, baseEnd_2884670] using wordTrace_append hprefix tailTrace_2884670
  have hstable : (prefixWord ++ tailWord_2884670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884670).length < 2 ^ (prefixWord ++ tailWord_2884670).sum := by decide
  have hdescent : baseEnd_2884670 < baseStart_2884670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884685 : List Nat := [1, 6, 1, 1, 1, 2, 4, 2, 4]
def baseStart_2884685 : Nat := 118140960795 + 2884685 * 2 ^ 59
def prefixEnd_2884685 : Nat := 4983230072969 + 3 ^ 40 * 2884685 * 2
def baseEnd_2884685 : Nat := 329162209292255864526907

theorem tailTrace_2884685 : CollatzResearch.WordTrace tailWord_2884685 prefixEnd_2884685 329162209292255864526907 := by
  unfold tailWord_2884685
  simp only [CollatzResearch.WordTrace]
  refine ⟨105213105554286384820047509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70142070369524256546698339 105213105554286384820047509)
  ·
    refine ⟨4931864322857174288439727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105213105554286384820047509 4931864322857174288439727)
    ·
      refine ⟨7397796484285761432659591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4931864322857174288439727 7397796484285761432659591)
      ·
        refine ⟨11096694726428642148989387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7397796484285761432659591 11096694726428642148989387)
        ·
          refine ⟨16645042089642963223484081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11096694726428642148989387 16645042089642963223484081)
          ·
            refine ⟨12483781567232222417613061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16645042089642963223484081 12483781567232222417613061)
            ·
              refine ⟨2340709043856041703302449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12483781567232222417613061 2340709043856041703302449)
              ·
                refine ⟨1755531782892031277476837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2340709043856041703302449 1755531782892031277476837)
                ·
                  refine ⟨329162209292255864526907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1755531782892031277476837 329162209292255864526907)
                  ·
                    rfl

theorem cell22_2884685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_2884685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884685 prefixEnd_2884685 := by exact prefixLift 2884685
  have htrace : WordTrace (prefixWord ++ tailWord_2884685) baseStart_2884685 baseEnd_2884685 := by
    simpa [prefixWord, tailWord_2884685, baseEnd_2884685] using wordTrace_append hprefix tailTrace_2884685
  have hstable : (prefixWord ++ tailWord_2884685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884685).length < 2 ^ (prefixWord ++ tailWord_2884685).sum := by decide
  have hdescent : baseEnd_2884685 < baseStart_2884685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884709 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 2, 6]
def baseStart_2884709 : Nat := 118140960795 + 2884709 * 2 ^ 59
def prefixEnd_2884709 : Nat := 4983230072969 + 3 ^ 40 * 2884709 * 2
def baseEnd_2884709 : Nat := 987494843567239530980647

theorem tailTrace_2884709 : CollatzResearch.WordTrace tailWord_2884709 prefixEnd_2884709 987494843567239530980647 := by
  unfold tailWord_2884709
  simp only [CollatzResearch.WordTrace]
  refine ⟨105213980906199436918921181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70142653937466291279280787 105213980906199436918921181)
  ·
    refine ⟨39455242839824788844595443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105213980906199436918921181 39455242839824788844595443)
    ·
      refine ⟨59182864259737183266893165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39455242839824788844595443 59182864259737183266893165)
      ·
        refine ⟨22193574097401443725084937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59182864259737183266893165 22193574097401443725084937)
        ·
          refine ⟨16645180573051082793813703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22193574097401443725084937 16645180573051082793813703)
          ·
            refine ⟨24967770859576624190720555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16645180573051082793813703 24967770859576624190720555)
            ·
              refine ⟨37451656289364936286080833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24967770859576624190720555 37451656289364936286080833)
              ·
                refine ⟨28088742217023702214560625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37451656289364936286080833 28088742217023702214560625)
                ·
                  refine ⟨21066556662767776660920469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28088742217023702214560625 21066556662767776660920469)
                  ·
                    refine ⟨987494843567239530980647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21066556662767776660920469 987494843567239530980647)
                    ·
                      rfl

theorem cell22_2884709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_2884709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884709 prefixEnd_2884709 := by exact prefixLift 2884709
  have htrace : WordTrace (prefixWord ++ tailWord_2884709) baseStart_2884709 baseEnd_2884709 := by
    simpa [prefixWord, tailWord_2884709, baseEnd_2884709] using wordTrace_append hprefix tailTrace_2884709
  have hstable : (prefixWord ++ tailWord_2884709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884709).length < 2 ^ (prefixWord ++ tailWord_2884709).sum := by decide
  have hdescent : baseEnd_2884709 < baseStart_2884709 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884711 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 5, 3]
def baseStart_2884711 : Nat := 118140960795 + 2884711 * 2 ^ 59
def prefixEnd_2884711 : Nat := 4983230072969 + 3 ^ 40 * 2884711 * 2
def baseEnd_2884711 : Nat := 987495528208112192430641

theorem tailTrace_2884711 : CollatzResearch.WordTrace tailWord_2884711 prefixEnd_2884711 987495528208112192430641 := by
  unfold tailWord_2884711
  simp only [CollatzResearch.WordTrace]
  refine ⟨105214053852192191260493987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70142702568128127506995991 105214053852192191260493987)
  ·
    refine ⟨157821080778288286890740981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105214053852192191260493987 157821080778288286890740981)
    ·
      refine ⟨14795726322964526896006967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157821080778288286890740981 14795726322964526896006967)
      ·
        refine ⟨22193589484446790344010451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14795726322964526896006967 22193589484446790344010451)
        ·
          refine ⟨33290384226670185516015677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22193589484446790344010451 33290384226670185516015677)
          ·
            refine ⟨12483894085001319568505879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33290384226670185516015677 12483894085001319568505879)
            ·
              refine ⟨18725841127501979352758819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12483894085001319568505879 18725841127501979352758819)
              ·
                refine ⟨28088761691252969029138229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18725841127501979352758819 28088761691252969029138229)
                ·
                  refine ⟨2633321408554965846481709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28088761691252969029138229 2633321408554965846481709)
                  ·
                    refine ⟨987495528208112192430641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2633321408554965846481709 987495528208112192430641)
                    ·
                      rfl

theorem cell22_2884711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 5, 3].length) (baseStart_2884711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884711 prefixEnd_2884711 := by exact prefixLift 2884711
  have htrace : WordTrace (prefixWord ++ tailWord_2884711) baseStart_2884711 baseEnd_2884711 := by
    simpa [prefixWord, tailWord_2884711, baseEnd_2884711] using wordTrace_append hprefix tailTrace_2884711
  have hstable : (prefixWord ++ tailWord_2884711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884711).length < 2 ^ (prefixWord ++ tailWord_2884711).sum := by decide
  have hdescent : baseEnd_2884711 < baseStart_2884711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884728 : List Nat := [2, 1, 2, 1, 1, 1, 5, 5, 1, 3]
def baseStart_2884728 : Nat := 118140960795 + 2884728 * 2 ^ 59
def prefixEnd_2884728 : Nat := 4983230072969 + 3 ^ 40 * 2884728 * 2
def baseEnd_2884728 : Nat := 987501347655529814755589

theorem tailTrace_2884728 : CollatzResearch.WordTrace tailWord_2884728 prefixEnd_2884728 987501347655529814755589 := by
  unfold tailWord_2884728
  simp only [CollatzResearch.WordTrace]
  refine ⟨52607336946565301581931419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70143115928753735442575225 52607336946565301581931419)
  ·
    refine ⟨78911005419847952372897129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52607336946565301581931419 78911005419847952372897129)
    ·
      refine ⟨59183254064885964279672847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78911005419847952372897129 59183254064885964279672847)
      ·
        refine ⟨88774881097328946419509271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59183254064885964279672847 88774881097328946419509271)
        ·
          refine ⟨133162321645993419629263907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88774881097328946419509271 133162321645993419629263907)
          ·
            refine ⟨199743482468990129443895861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133162321645993419629263907 199743482468990129443895861)
            ·
              refine ⟨18725951481467824635365237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 199743482468990129443895861 18725951481467824635365237)
              ·
                refine ⟨1755557951387608559565491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18725951481467824635365237 1755557951387608559565491)
                ·
                  refine ⟨2633336927081412839348237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1755557951387608559565491 2633336927081412839348237)
                  ·
                    refine ⟨987501347655529814755589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2633336927081412839348237 987501347655529814755589)
                    ·
                      rfl

theorem cell22_2884728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_2884728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884728 prefixEnd_2884728 := by exact prefixLift 2884728
  have htrace : WordTrace (prefixWord ++ tailWord_2884728) baseStart_2884728 baseEnd_2884728 := by
    simpa [prefixWord, tailWord_2884728, baseEnd_2884728] using wordTrace_append hprefix tailTrace_2884728
  have hstable : (prefixWord ++ tailWord_2884728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884728).length < 2 ^ (prefixWord ++ tailWord_2884728).sum := by decide
  have hdescent : baseEnd_2884728 < baseStart_2884728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884739 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 4, 5]
def baseStart_2884739 : Nat := 118140960795 + 2884739 * 2 ^ 59
def prefixEnd_2884739 : Nat := 4983230072969 + 3 ^ 40 * 2884739 * 2
def baseEnd_2884739 : Nat := 987505113180329452730555

theorem tailTrace_2884739 : CollatzResearch.WordTrace tailWord_2884739 prefixEnd_2884739 987505113180329452730555 := by
  unfold tailWord_2884739
  simp only [CollatzResearch.WordTrace]
  refine ⟨105215075096090752042513271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70143383397393834695008847 105215075096090752042513271)
  ·
    refine ⟨157822612644136128063769907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105215075096090752042513271 157822612644136128063769907)
    ·
      refine ⟨236733918966204192095654861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157822612644136128063769907 236733918966204192095654861)
      ·
        refine ⟨88775219612326572035870573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236733918966204192095654861 88775219612326572035870573)
        ·
          refine ⟨33290707354622464513451465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88775219612326572035870573 33290707354622464513451465)
          ·
            refine ⟨24968030515966848385088599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33290707354622464513451465 24968030515966848385088599)
            ·
              refine ⟨37452045773950272577632899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24968030515966848385088599 37452045773950272577632899)
              ·
                refine ⟨56178068660925408866449349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37452045773950272577632899 56178068660925408866449349)
                ·
                  refine ⟨10533387873923514162459253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56178068660925408866449349 10533387873923514162459253)
                  ·
                    refine ⟨987505113180329452730555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10533387873923514162459253 987505113180329452730555)
                    ·
                      rfl

theorem cell22_2884739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 5].length) (baseStart_2884739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884739 prefixEnd_2884739 := by exact prefixLift 2884739
  have htrace : WordTrace (prefixWord ++ tailWord_2884739) baseStart_2884739 baseEnd_2884739 := by
    simpa [prefixWord, tailWord_2884739, baseEnd_2884739] using wordTrace_append hprefix tailTrace_2884739
  have hstable : (prefixWord ++ tailWord_2884739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884739).length < 2 ^ (prefixWord ++ tailWord_2884739).sum := by decide
  have hdescent : baseEnd_2884739 < baseStart_2884739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884741 : List Nat := [1, 3, 1, 1, 6, 1, 1, 1, 7]
def baseStart_2884741 : Nat := 118140960795 + 2884741 * 2 ^ 59
def prefixEnd_2884741 : Nat := 4983230072969 + 3 ^ 40 * 2884741 * 2
def baseEnd_2884741 : Nat := 329168599273734038060183

theorem tailTrace_2884741 : CollatzResearch.WordTrace tailWord_2884741 prefixEnd_2884741 329168599273734038060183 := by
  unfold tailWord_2884741
  simp only [CollatzResearch.WordTrace]
  refine ⟨105215148042083506384086077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70143432028055670922724051 105215148042083506384086077)
  ·
    refine ⟨39455680515781314894032279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105215148042083506384086077 39455680515781314894032279)
    ·
      refine ⟨59183520773671972341048419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39455680515781314894032279 59183520773671972341048419)
      ·
        refine ⟨88775281160507958511572629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59183520773671972341048419 88775281160507958511572629)
        ·
          refine ⟨4161341304398810555229967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88775281160507958511572629 4161341304398810555229967)
          ·
            refine ⟨6242011956598215832844951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161341304398810555229967 6242011956598215832844951)
            ·
              refine ⟨9363017934897323749267427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6242011956598215832844951 9363017934897323749267427)
              ·
                refine ⟨14044526902345985623901141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9363017934897323749267427 14044526902345985623901141)
                ·
                  refine ⟨329168599273734038060183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14044526902345985623901141 329168599273734038060183)
                  ·
                    rfl

theorem cell22_2884741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_2884741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884741 prefixEnd_2884741 := by exact prefixLift 2884741
  have htrace : WordTrace (prefixWord ++ tailWord_2884741) baseStart_2884741 baseEnd_2884741 := by
    simpa [prefixWord, tailWord_2884741, baseEnd_2884741] using wordTrace_append hprefix tailTrace_2884741
  have hstable : (prefixWord ++ tailWord_2884741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884741).length < 2 ^ (prefixWord ++ tailWord_2884741).sum := by decide
  have hdescent : baseEnd_2884741 < baseStart_2884741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884833 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 2, 4]
def baseStart_2884833 : Nat := 118140960795 + 2884833 * 2 ^ 59
def prefixEnd_2884833 : Nat := 4983230072969 + 3 ^ 40 * 2884833 * 2
def baseEnd_2884833 : Nat := 987537291301344540880267

theorem tailTrace_2884833 : CollatzResearch.WordTrace tailWord_2884833 prefixEnd_2884833 987537291301344540880267 := by
  unfold tailWord_2884833
  simp only [CollatzResearch.WordTrace]
  refine ⟨105218503557750206096435153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70145669038500137397623435 105218503557750206096435153)
  ·
    refine ⟨78913877668312654572326365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105218503557750206096435153 78913877668312654572326365)
    ·
      refine ⟨29592704125617245464622387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78913877668312654572326365 29592704125617245464622387)
      ·
        refine ⟨44389056188425868196933581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29592704125617245464622387 44389056188425868196933581)
        ·
          refine ⟨16645896070659700573850093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44389056188425868196933581 16645896070659700573850093)
          ·
            refine ⟨6242211026497387715193785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16645896070659700573850093 6242211026497387715193785)
            ·
              refine ⟨4681658269873040786395339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6242211026497387715193785 4681658269873040786395339)
              ·
                refine ⟨7022487404809561179593009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4681658269873040786395339 7022487404809561179593009)
                ·
                  refine ⟨5266865553607170884694757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7022487404809561179593009 5266865553607170884694757)
                  ·
                    refine ⟨987537291301344540880267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5266865553607170884694757 987537291301344540880267)
                    ·
                      rfl

theorem cell22_2884833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 4].length) (baseStart_2884833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884833 prefixEnd_2884833 := by exact prefixLift 2884833
  have htrace : WordTrace (prefixWord ++ tailWord_2884833) baseStart_2884833 baseEnd_2884833 := by
    simpa [prefixWord, tailWord_2884833, baseEnd_2884833] using wordTrace_append hprefix tailTrace_2884833
  have hstable : (prefixWord ++ tailWord_2884833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884833).length < 2 ^ (prefixWord ++ tailWord_2884833).sum := by decide
  have hdescent : baseEnd_2884833 < baseStart_2884833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884882 : List Nat := [3, 2, 4, 2, 1, 1, 3, 6]
def baseStart_2884882 : Nat := 118140960795 + 2884882 * 2 ^ 59
def prefixEnd_2884882 : Nat := 4983230072969 + 3 ^ 40 * 2884882 * 2
def baseEnd_2884882 : Nat := 109728229444747194045013

theorem tailTrace_2884882 : CollatzResearch.WordTrace tailWord_2884882 prefixEnd_2884882 109728229444747194045013 := by
  unfold tailWord_2884882
  simp only [CollatzResearch.WordTrace]
  refine ⟨26305072683643171866242225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70146860489715124976645933 26305072683643171866242225)
  ·
    refine ⟨19728804512732378899681669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26305072683643171866242225 19728804512732378899681669)
    ·
      refine ⟨3699150846137321043690313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19728804512732378899681669 3699150846137321043690313)
      ·
        refine ⟨2774363134602990782767735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3699150846137321043690313 2774363134602990782767735)
        ·
          refine ⟨4161544701904486174151603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774363134602990782767735 4161544701904486174151603)
          ·
            refine ⟨6242317052856729261227405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4161544701904486174151603 6242317052856729261227405)
            ·
              refine ⟨2340868894821273472960277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6242317052856729261227405 2340868894821273472960277)
              ·
                refine ⟨109728229444747194045013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2340868894821273472960277 109728229444747194045013)
                ·
                  rfl

theorem cell22_2884882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 6].length) (baseStart_2884882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884882 prefixEnd_2884882 := by exact prefixLift 2884882
  have htrace : WordTrace (prefixWord ++ tailWord_2884882) baseStart_2884882 baseEnd_2884882 := by
    simpa [prefixWord, tailWord_2884882, baseEnd_2884882] using wordTrace_append hprefix tailTrace_2884882
  have hstable : (prefixWord ++ tailWord_2884882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884882).length < 2 ^ (prefixWord ++ tailWord_2884882).sum := by decide
  have hdescent : baseEnd_2884882 < baseStart_2884882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884940 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 1, 4]
def baseStart_2884940 : Nat := 118140960795 + 2884940 * 2 ^ 59
def prefixEnd_2884940 : Nat := 4983230072969 + 3 ^ 40 * 2884940 * 2
def baseEnd_2884940 : Nat := 987573919588031928454939

theorem tailTrace_2884940 : CollatzResearch.WordTrace tailWord_2884940 prefixEnd_2884940 987573919588031928454939 := by
  unfold tailWord_2884940
  simp only [CollatzResearch.WordTrace]
  refine ⟨52611203084181281685290137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70148270778908375580386849 52611203084181281685290137)
  ·
    refine ⟨39458402313135961263967603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52611203084181281685290137 39458402313135961263967603)
    ·
      refine ⟨59187603469703941895951405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39458402313135961263967603 59187603469703941895951405)
      ·
        refine ⟨22195351301138978210981777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59187603469703941895951405 22195351301138978210981777)
        ·
          refine ⟨16646513475854233658236333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22195351301138978210981777 16646513475854233658236333)
          ·
            refine ⟨6242442553445337621838625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16646513475854233658236333 6242442553445337621838625)
            ·
              refine ⟨4681831915084003216378969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6242442553445337621838625 4681831915084003216378969)
              ·
                refine ⟨3511373936313002412284227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4681831915084003216378969 3511373936313002412284227)
                ·
                  refine ⟨5267060904469503618426341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511373936313002412284227 5267060904469503618426341)
                  ·
                    refine ⟨987573919588031928454939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5267060904469503618426341 987573919588031928454939)
                    ·
                      rfl

theorem cell22_2884940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 4].length) (baseStart_2884940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884940 prefixEnd_2884940 := by exact prefixLift 2884940
  have htrace : WordTrace (prefixWord ++ tailWord_2884940) baseStart_2884940 baseEnd_2884940 := by
    simpa [prefixWord, tailWord_2884940, baseEnd_2884940] using wordTrace_append hprefix tailTrace_2884940
  have hstable : (prefixWord ++ tailWord_2884940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884940).length < 2 ^ (prefixWord ++ tailWord_2884940).sum := by decide
  have hdescent : baseEnd_2884940 < baseStart_2884940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884953 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 4, 3]
def baseStart_2884953 : Nat := 118140960795 + 2884953 * 2 ^ 59
def prefixEnd_2884953 : Nat := 4983230072969 + 3 ^ 40 * 2884953 * 2
def baseEnd_2884953 : Nat := 987578369753704227879899

theorem tailTrace_2884953 : CollatzResearch.WordTrace tailWord_2884953 prefixEnd_2884953 987578369753704227879899 := by
  unfold tailWord_2884953
  simp only [CollatzResearch.WordTrace]
  refine ⟨105222880317315466590803513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70148586878210311060535675 105222880317315466590803513)
  ·
    refine ⟨78917160237986599943102635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105222880317315466590803513 78917160237986599943102635)
    ·
      refine ⟨118375740356979899914653953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78917160237986599943102635 118375740356979899914653953)
      ·
        refine ⟨88781805267734924935990465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118375740356979899914653953 88781805267734924935990465)
        ·
          refine ⟨66586353950801193701992849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88781805267734924935990465 66586353950801193701992849)
          ·
            refine ⟨49939765463100895276494637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66586353950801193701992849 49939765463100895276494637)
            ·
              refine ⟨18727412048662835728685489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49939765463100895276494637 18727412048662835728685489)
              ·
                refine ⟨14045559036497126796514117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18727412048662835728685489 14045559036497126796514117)
                ·
                  refine ⟨2633542319343211274346397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14045559036497126796514117 2633542319343211274346397)
                  ·
                    refine ⟨987578369753704227879899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2633542319343211274346397 987578369753704227879899)
                    ·
                      rfl

theorem cell22_2884953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 4, 3].length) (baseStart_2884953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884953 prefixEnd_2884953 := by exact prefixLift 2884953
  have htrace : WordTrace (prefixWord ++ tailWord_2884953) baseStart_2884953 baseEnd_2884953 := by
    simpa [prefixWord, tailWord_2884953, baseEnd_2884953] using wordTrace_append hprefix tailTrace_2884953
  have hstable : (prefixWord ++ tailWord_2884953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884953).length < 2 ^ (prefixWord ++ tailWord_2884953).sum := by decide
  have hdescent : baseEnd_2884953 < baseStart_2884953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2884972 : List Nat := [2, 2, 1, 1, 5, 2, 3, 2, 4]
def baseStart_2884972 : Nat := 118140960795 + 2884972 * 2 ^ 59
def prefixEnd_2884972 : Nat := 4983230072969 + 3 ^ 40 * 2884972 * 2
def baseEnd_2884972 : Nat := 329194957947331503884947

theorem tailTrace_2884972 : CollatzResearch.WordTrace tailWord_2884972 prefixEnd_2884972 329194957947331503884947 := by
  unfold tailWord_2884972
  simp only [CollatzResearch.WordTrace]
  refine ⟨52611786652123316417872585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70149048869497755223830113 52611786652123316417872585)
  ·
    refine ⟨39458839989092487313404439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52611786652123316417872585 39458839989092487313404439)
    ·
      refine ⟨59188259983638730970106659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39458839989092487313404439 59188259983638730970106659)
      ·
        refine ⟨88782389975458096455159989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59188259983638730970106659 88782389975458096455159989)
        ·
          refine ⟨8323349060199196542671249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88782389975458096455159989 8323349060199196542671249)
          ·
            refine ⟨6242511795149397407003437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8323349060199196542671249 6242511795149397407003437)
            ·
              refine ⟨2340941923181024027626289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6242511795149397407003437 2340941923181024027626289)
              ·
                refine ⟨1755706442385768020719717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2340941923181024027626289 1755706442385768020719717)
                ·
                  refine ⟨329194957947331503884947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1755706442385768020719717 329194957947331503884947)
                  ·
                    rfl

theorem cell22_2884972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 3, 2, 4].length) (baseStart_2884972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2884972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2884972 prefixEnd_2884972 := by exact prefixLift 2884972
  have htrace : WordTrace (prefixWord ++ tailWord_2884972) baseStart_2884972 baseEnd_2884972 := by
    simpa [prefixWord, tailWord_2884972, baseEnd_2884972] using wordTrace_append hprefix tailTrace_2884972
  have hstable : (prefixWord ++ tailWord_2884972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2884972).length < 2 ^ (prefixWord ++ tailWord_2884972).sum := by decide
  have hdescent : baseEnd_2884972 < baseStart_2884972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2884972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885045 : List Nat := [1, 3, 3, 2, 2, 1, 2, 3, 5]
def baseStart_2885045 : Nat := 118140960795 + 2885045 * 2 ^ 59
def prefixEnd_2885045 : Nat := 4983230072969 + 3 ^ 40 * 2885045 * 2
def baseEnd_2885045 : Nat := 329203287744615551526539

theorem tailTrace_2885045 : CollatzResearch.WordTrace tailWord_2885045 prefixEnd_2885045 329203287744615551526539 := by
  unfold tailWord_2885045
  simp only [CollatzResearch.WordTrace]
  refine ⟨105226235832982166303152589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70150823888654777535435059 105226235832982166303152589)
  ·
    refine ⟨39459838437368312363682221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105226235832982166303152589 39459838437368312363682221)
    ·
      refine ⟨14797439414013117136380833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39459838437368312363682221 14797439414013117136380833)
      ·
        refine ⟨11098079560509837852285625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14797439414013117136380833 11098079560509837852285625)
        ·
          refine ⟨8323559670382378389214219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11098079560509837852285625 8323559670382378389214219)
          ·
            refine ⟨12485339505573567583821329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8323559670382378389214219 12485339505573567583821329)
            ·
              refine ⟨9364004629180175687865997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12485339505573567583821329 9364004629180175687865997)
              ·
                refine ⟨3511501735942565882949749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9364004629180175687865997 3511501735942565882949749)
                ·
                  refine ⟨329203287744615551526539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3511501735942565882949749 329203287744615551526539)
                  ·
                    rfl

theorem cell22_2885045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 2, 3, 5].length) (baseStart_2885045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885045 prefixEnd_2885045 := by exact prefixLift 2885045
  have htrace : WordTrace (prefixWord ++ tailWord_2885045) baseStart_2885045 baseEnd_2885045 := by
    simpa [prefixWord, tailWord_2885045, baseEnd_2885045] using wordTrace_append hprefix tailTrace_2885045
  have hstable : (prefixWord ++ tailWord_2885045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885045).length < 2 ^ (prefixWord ++ tailWord_2885045).sum := by decide
  have hdescent : baseEnd_2885045 < baseStart_2885045 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885103 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 1, 6]
def baseStart_2885103 : Nat := 118140960795 + 2885103 * 2 ^ 59
def prefixEnd_2885103 : Nat := 4983230072969 + 3 ^ 40 * 2885103 * 2
def baseEnd_2885103 : Nat := 987629717819153836629439

theorem tailTrace_2885103 : CollatzResearch.WordTrace tailWord_2885103 prefixEnd_2885103 987629717819153836629439 := by
  unfold tailWord_2885103
  simp only [CollatzResearch.WordTrace]
  refine ⟨105228351266772042208763963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70152234177848028139175975 105228351266772042208763963)
  ·
    refine ⟨157842526900158063313145945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105228351266772042208763963 157842526900158063313145945)
    ·
      refine ⟨118381895175118547484859459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157842526900158063313145945 118381895175118547484859459)
      ·
        refine ⟨177572842762677821227289189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118381895175118547484859459 177572842762677821227289189)
        ·
          refine ⟨33294908018002091480116723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177572842762677821227289189 33294908018002091480116723)
          ·
            refine ⟨49942362027003137220175085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33294908018002091480116723 49942362027003137220175085)
            ·
              refine ⟨18728385760126176457565657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49942362027003137220175085 18728385760126176457565657)
              ·
                refine ⟨14046289320094632343174243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18728385760126176457565657 14046289320094632343174243)
                ·
                  refine ⟨21069433980141948514761365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14046289320094632343174243 21069433980141948514761365)
                  ·
                    refine ⟨987629717819153836629439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21069433980141948514761365 987629717819153836629439)
                    ·
                      rfl

theorem cell22_2885103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_2885103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885103 prefixEnd_2885103 := by exact prefixLift 2885103
  have htrace : WordTrace (prefixWord ++ tailWord_2885103) baseStart_2885103 baseEnd_2885103 := by
    simpa [prefixWord, tailWord_2885103, baseEnd_2885103] using wordTrace_append hprefix tailTrace_2885103
  have hstable : (prefixWord ++ tailWord_2885103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885103).length < 2 ^ (prefixWord ++ tailWord_2885103).sum := by decide
  have hdescent : baseEnd_2885103 < baseStart_2885103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885105 : List Nat := [1, 2, 2, 2, 3, 2, 3, 1, 1, 5]
def baseStart_2885105 : Nat := 118140960795 + 2885105 * 2 ^ 59
def prefixEnd_2885105 : Nat := 4983230072969 + 3 ^ 40 * 2885105 * 2
def baseEnd_2885105 : Nat := 987630402460026498079433

theorem tailTrace_2885105 : CollatzResearch.WordTrace tailWord_2885105 prefixEnd_2885105 987630402460026498079433 := by
  unfold tailWord_2885105
  simp only [CollatzResearch.WordTrace]
  refine ⟨105228424212764796550336769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70152282808509864366891179 105228424212764796550336769)
  ·
    refine ⟨78921318159573597412752577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105228424212764796550336769 78921318159573597412752577)
    ·
      refine ⟨59190988619680198059564433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78921318159573597412752577 59190988619680198059564433)
      ·
        refine ⟨44393241464760148544673325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59190988619680198059564433 44393241464760148544673325)
        ·
          refine ⟨16647465549285055704252497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44393241464760148544673325 16647465549285055704252497)
          ·
            refine ⟨12485599161963791778189373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16647465549285055704252497 12485599161963791778189373)
            ·
              refine ⟨4682099685736421916821015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12485599161963791778189373 4682099685736421916821015)
              ·
                refine ⟨7023149528604632875231523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4682099685736421916821015 7023149528604632875231523)
                ·
                  refine ⟨10534724292906949312847285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7023149528604632875231523 10534724292906949312847285)
                  ·
                    refine ⟨987630402460026498079433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10534724292906949312847285 987630402460026498079433)
                    ·
                      rfl

theorem cell22_2885105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 3, 1, 1, 5].length) (baseStart_2885105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885105 prefixEnd_2885105 := by exact prefixLift 2885105
  have htrace : WordTrace (prefixWord ++ tailWord_2885105) baseStart_2885105 baseEnd_2885105 := by
    simpa [prefixWord, tailWord_2885105, baseEnd_2885105] using wordTrace_append hprefix tailTrace_2885105
  have hstable : (prefixWord ++ tailWord_2885105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885105).length < 2 ^ (prefixWord ++ tailWord_2885105).sum := by decide
  have hdescent : baseEnd_2885105 < baseStart_2885105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885109 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 1, 4]
def baseStart_2885109 : Nat := 118140960795 + 2885109 * 2 ^ 59
def prefixEnd_2885109 : Nat := 4983230072969 + 3 ^ 40 * 2885109 * 2
def baseEnd_2885109 : Nat := 987631771741771820979421

theorem tailTrace_2885109 : CollatzResearch.WordTrace tailWord_2885109 prefixEnd_2885109 987631771741771820979421 := by
  unfold tailWord_2885109
  simp only [CollatzResearch.WordTrace]
  refine ⟨105228570104750305233482381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70152380069833536822321587 105228570104750305233482381)
  ·
    refine ⟨39460713789281364462555893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105228570104750305233482381 39460713789281364462555893)
    ·
      refine ⟨3699441917745127918364615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39460713789281364462555893 3699441917745127918364615)
      ·
        refine ⟨5549162876617691877546923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699441917745127918364615 5549162876617691877546923)
        ·
          refine ⟨8323744314926537816320385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5549162876617691877546923 8323744314926537816320385)
          ·
            refine ⟨6242808236194903362240289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8323744314926537816320385 6242808236194903362240289)
            ·
              refine ⟨4682106177146177521680217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6242808236194903362240289 4682106177146177521680217)
              ·
                refine ⟨3511579632859633141260163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4682106177146177521680217 3511579632859633141260163)
                ·
                  refine ⟨5267369449289449711890245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3511579632859633141260163 5267369449289449711890245)
                  ·
                    refine ⟨987631771741771820979421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5267369449289449711890245 987631771741771820979421)
                    ·
                      rfl

theorem cell22_2885109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_2885109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885109 prefixEnd_2885109 := by exact prefixLift 2885109
  have htrace : WordTrace (prefixWord ++ tailWord_2885109) baseStart_2885109 baseEnd_2885109 := by
    simpa [prefixWord, tailWord_2885109, baseEnd_2885109] using wordTrace_append hprefix tailTrace_2885109
  have hstable : (prefixWord ++ tailWord_2885109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885109).length < 2 ^ (prefixWord ++ tailWord_2885109).sum := by decide
  have hdescent : baseEnd_2885109 < baseStart_2885109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885212 : List Nat := [2, 2, 4, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2885212 : Nat := 118140960795 + 2885212 * 2 ^ 59
def prefixEnd_2885212 : Nat := 4983230072969 + 3 ^ 40 * 2885212 * 2
def baseEnd_2885212 : Nat := 987667030746713885654105

theorem tailTrace_2885212 : CollatzResearch.WordTrace tailWord_2885212 prefixEnd_2885212 987667030746713885654105 := by
  unfold tailWord_2885212
  simp only [CollatzResearch.WordTrace]
  refine ⟨52616163411688576912240945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70154884548918102549654593 52616163411688576912240945)
  ·
    refine ⟨39462122558766432684180709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52616163411688576912240945 39462122558766432684180709)
    ·
      refine ⟨7399147979768706128283883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39462122558766432684180709 7399147979768706128283883)
      ·
        refine ⟨11098721969653059192425825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7399147979768706128283883 11098721969653059192425825)
        ·
          refine ⟨8324041477239794394319369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11098721969653059192425825 8324041477239794394319369)
          ·
            refine ⟨6243031107929845795739527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8324041477239794394319369 6243031107929845795739527)
            ·
              refine ⟨9364546661894768693609291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243031107929845795739527 9364546661894768693609291)
              ·
                refine ⟨14046819992842153040413937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9364546661894768693609291 14046819992842153040413937)
                ·
                  refine ⟨10535114994631614780310453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14046819992842153040413937 10535114994631614780310453)
                  ·
                    refine ⟨987667030746713885654105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10535114994631614780310453 987667030746713885654105)
                    ·
                      rfl

theorem cell22_2885212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2885212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885212 prefixEnd_2885212 := by exact prefixLift 2885212
  have htrace : WordTrace (prefixWord ++ tailWord_2885212) baseStart_2885212 baseEnd_2885212 := by
    simpa [prefixWord, tailWord_2885212, baseEnd_2885212] using wordTrace_append hprefix tailTrace_2885212
  have hstable : (prefixWord ++ tailWord_2885212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885212).length < 2 ^ (prefixWord ++ tailWord_2885212).sum := by decide
  have hdescent : baseEnd_2885212 < baseStart_2885212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885325 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2885325 : Nat := 118140960795 + 2885325 * 2 ^ 59
def prefixEnd_2885325 : Nat := 4983230072969 + 3 ^ 40 * 2885325 * 2
def baseEnd_2885325 : Nat := 987705712956019257578759

theorem tailTrace_2885325 : CollatzResearch.WordTrace tailWord_2885325 prefixEnd_2885325 987705712956019257578759 := by
  unfold tailWord_2885325
  simp only [CollatzResearch.WordTrace]
  refine ⟨105236448271967774123345429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70157632181311849415563619 105236448271967774123345429)
  ·
    refine ⟨4932958512748489412031817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105236448271967774123345429 4932958512748489412031817)
    ·
      refine ⟨3699718884561367059023863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4932958512748489412031817 3699718884561367059023863)
      ·
        refine ⟨5549578326842050588535795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699718884561367059023863 5549578326842050588535795)
        ·
          refine ⟨8324367490263075882803693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5549578326842050588535795 8324367490263075882803693)
          ·
            refine ⟨3121637808848653456051385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8324367490263075882803693 3121637808848653456051385)
            ·
              refine ⟨2341228356636490092038539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3121637808848653456051385 2341228356636490092038539)
              ·
                refine ⟨3511842534954735138057809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341228356636490092038539 3511842534954735138057809)
                ·
                  refine ⟨2633881901216051353543357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3511842534954735138057809 2633881901216051353543357)
                  ·
                    refine ⟨987705712956019257578759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2633881901216051353543357 987705712956019257578759)
                    ·
                      rfl

theorem cell22_2885325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2885325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885325 prefixEnd_2885325 := by exact prefixLift 2885325
  have htrace : WordTrace (prefixWord ++ tailWord_2885325) baseStart_2885325 baseEnd_2885325 := by
    simpa [prefixWord, tailWord_2885325, baseEnd_2885325] using wordTrace_append hprefix tailTrace_2885325
  have hstable : (prefixWord ++ tailWord_2885325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885325).length < 2 ^ (prefixWord ++ tailWord_2885325).sum := by decide
  have hdescent : baseEnd_2885325 < baseStart_2885325 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885360 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 10]
def baseStart_2885360 : Nat := 118140960795 + 2885360 * 2 ^ 59
def prefixEnd_2885360 : Nat := 4983230072969 + 3 ^ 40 * 2885360 * 2
def baseEnd_2885360 : Nat := 329239231390430277651217

theorem tailTrace_2885360 : CollatzResearch.WordTrace tailWord_2885360 prefixEnd_2885360 329239231390430277651217 := by
  unfold tailWord_2885360
  simp only [CollatzResearch.WordTrace]
  refine ⟨52618862413420487550434767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70158483217893983400579689 52618862413420487550434767)
  ·
    refine ⟨78928293620130731325652151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52618862413420487550434767 78928293620130731325652151)
    ·
      refine ⟨118392440430196096988478227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78928293620130731325652151 118392440430196096988478227)
      ·
        refine ⟨177588660645294145482717341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118392440430196096988478227 177588660645294145482717341)
        ·
          refine ⟨66595747741985304556019003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177588660645294145482717341 66595747741985304556019003)
          ·
            refine ⟨99893621612977956834028505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66595747741985304556019003 99893621612977956834028505)
            ·
              refine ⟨74920216209733467625521379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99893621612977956834028505 74920216209733467625521379)
              ·
                refine ⟨112380324314600201438282069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74920216209733467625521379 112380324314600201438282069)
                ·
                  refine ⟨329239231390430277651217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 112380324314600201438282069 329239231390430277651217)
                  ·
                    rfl

theorem cell22_2885360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 10].length) (baseStart_2885360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885360 prefixEnd_2885360 := by exact prefixLift 2885360
  have htrace : WordTrace (prefixWord ++ tailWord_2885360) baseStart_2885360 baseEnd_2885360 := by
    simpa [prefixWord, tailWord_2885360, baseEnd_2885360] using wordTrace_append hprefix tailTrace_2885360
  have hstable : (prefixWord ++ tailWord_2885360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885360).length < 2 ^ (prefixWord ++ tailWord_2885360).sum := by decide
  have hdescent : baseEnd_2885360 < baseStart_2885360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885394 : List Nat := [3, 2, 4, 1, 1, 1, 1, 1, 8]
def baseStart_2885394 : Nat := 118140960795 + 2885394 * 2 ^ 59
def prefixEnd_2885394 : Nat := 4983230072969 + 3 ^ 40 * 2885394 * 2
def baseEnd_2885394 : Nat := 329243111022042025867849

theorem tailTrace_2885394 : CollatzResearch.WordTrace tailWord_2885394 prefixEnd_2885394 329243111022042025867849 := by
  unfold tailWord_2885394
  simp only [CollatzResearch.WordTrace]
  refine ⟨26309741227179449726901809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70159309939145199271738157 26309741227179449726901809)
  ·
    refine ⟨19732305920384587295176357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26309741227179449726901809 19732305920384587295176357)
    ·
      refine ⟨3699807360072110117845567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19732305920384587295176357 3699807360072110117845567)
      ·
        refine ⟨5549711040108165176768351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3699807360072110117845567 5549711040108165176768351)
        ·
          refine ⟨8324566560162247765152527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5549711040108165176768351 8324566560162247765152527)
          ·
            refine ⟨12486849840243371647728791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8324566560162247765152527 12486849840243371647728791)
            ·
              refine ⟨18730274760365057471593187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12486849840243371647728791 18730274760365057471593187)
              ·
                refine ⟨28095412140547586207389781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18730274760365057471593187 28095412140547586207389781)
                ·
                  refine ⟨329243111022042025867849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28095412140547586207389781 329243111022042025867849)
                  ·
                    rfl

theorem cell22_2885394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 1, 8].length) (baseStart_2885394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885394 prefixEnd_2885394 := by exact prefixLift 2885394
  have htrace : WordTrace (prefixWord ++ tailWord_2885394) baseStart_2885394 baseEnd_2885394 := by
    simpa [prefixWord, tailWord_2885394, baseEnd_2885394] using wordTrace_append hprefix tailTrace_2885394
  have hstable : (prefixWord ++ tailWord_2885394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885394).length < 2 ^ (prefixWord ++ tailWord_2885394).sum := by decide
  have hdescent : baseEnd_2885394 < baseStart_2885394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885407 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 1, 6]
def baseStart_2885407 : Nat := 118140960795 + 2885407 * 2 ^ 59
def prefixEnd_2885407 : Nat := 4983230072969 + 3 ^ 40 * 2885407 * 2
def baseEnd_2885407 : Nat := 987733783231798377028507

theorem tailTrace_2885407 : CollatzResearch.WordTrace tailWord_2885407 prefixEnd_2885407 987733783231798377028507 := by
  unfold tailWord_2885407
  simp only [CollatzResearch.WordTrace]
  refine ⟨105239439057670702127830475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70159626038447134751886983 105239439057670702127830475)
  ·
    refine ⟨157859158586506053191745713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105239439057670702127830475 157859158586506053191745713)
    ·
      refine ⟨118394368939879539893809285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157859158586506053191745713 118394368939879539893809285)
      ·
        refine ⟨22198944176227413730089241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118394368939879539893809285 22198944176227413730089241)
        ·
          refine ⟨16649208132170560297566931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22198944176227413730089241 16649208132170560297566931)
          ·
            refine ⟨24973812198255840446350397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16649208132170560297566931 24973812198255840446350397)
            ·
              refine ⟨9365179574345940167381399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24973812198255840446350397 9365179574345940167381399)
              ·
                refine ⟨14047769361518910251072099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9365179574345940167381399 14047769361518910251072099)
                ·
                  refine ⟨21071654042278365376608149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14047769361518910251072099 21071654042278365376608149)
                  ·
                    refine ⟨987733783231798377028507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21071654042278365376608149 987733783231798377028507)
                    ·
                      rfl

theorem cell22_2885407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_2885407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885407 prefixEnd_2885407 := by exact prefixLift 2885407
  have htrace : WordTrace (prefixWord ++ tailWord_2885407) baseStart_2885407 baseEnd_2885407 := by
    simpa [prefixWord, tailWord_2885407, baseEnd_2885407] using wordTrace_append hprefix tailTrace_2885407
  have hstable : (prefixWord ++ tailWord_2885407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885407).length < 2 ^ (prefixWord ++ tailWord_2885407).sum := by decide
  have hdescent : baseEnd_2885407 < baseStart_2885407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885426 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 2, 3]
def baseStart_2885426 : Nat := 118140960795 + 2885426 * 2 ^ 59
def prefixEnd_2885426 : Nat := 4983230072969 + 3 ^ 40 * 2885426 * 2
def baseEnd_2885426 : Nat := 987740287320088660803449

theorem tailTrace_2885426 : CollatzResearch.WordTrace tailWord_2885426 prefixEnd_2885426 987740287320088660803449 := by
  unfold tailWord_2885426
  simp only [CollatzResearch.WordTrace]
  refine ⟨26310033011150467093193033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70160088029734578915181421 26310033011150467093193033)
  ·
    refine ⟨19732524758362850319894775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26310033011150467093193033 19732524758362850319894775)
    ·
      refine ⟨29598787137544275479842163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19732524758362850319894775 29598787137544275479842163)
      ·
        refine ⟨44398180706316413219763245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29598787137544275479842163 44398180706316413219763245)
        ·
          refine ⟨16649317764868654957411217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44398180706316413219763245 16649317764868654957411217)
          ·
            refine ⟨12486988323651491218058413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16649317764868654957411217 12486988323651491218058413)
            ·
              refine ⟨4682620621369309206771905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12486988323651491218058413 4682620621369309206771905)
              ·
                refine ⟨3511965466026981905078929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4682620621369309206771905 3511965466026981905078929)
                ·
                  refine ⟨2633974099520236428809197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3511965466026981905078929 2633974099520236428809197)
                  ·
                    refine ⟨987740287320088660803449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2633974099520236428809197 987740287320088660803449)
                    ·
                      rfl

theorem cell22_2885426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_2885426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885426 prefixEnd_2885426 := by exact prefixLift 2885426
  have htrace : WordTrace (prefixWord ++ tailWord_2885426) baseStart_2885426 baseEnd_2885426 := by
    simpa [prefixWord, tailWord_2885426, baseEnd_2885426] using wordTrace_append hprefix tailTrace_2885426
  have hstable : (prefixWord ++ tailWord_2885426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885426).length < 2 ^ (prefixWord ++ tailWord_2885426).sum := by decide
  have hdescent : baseEnd_2885426 < baseStart_2885426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885550 : List Nat := [4, 1, 5, 1, 1, 1, 1, 1, 2, 5]
def baseStart_2885550 : Nat := 118140960795 + 2885550 * 2 ^ 59
def prefixEnd_2885550 : Nat := 4983230072969 + 3 ^ 40 * 2885550 * 2
def baseEnd_2885550 : Nat := 987782735054193670703069

theorem tailTrace_2885550 : CollatzResearch.WordTrace tailWord_2885550 prefixEnd_2885550 987782735054193670703069 := by
  unfold tailWord_2885550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13155581837019079693785763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70163103130768425033524069 13155581837019079693785763)
  ·
    refine ⟨19733372755528619540678645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13155581837019079693785763 19733372755528619540678645)
    ·
      refine ⟨1850003695830808081938623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19733372755528619540678645 1850003695830808081938623)
      ·
        refine ⟨2775005543746212122907935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1850003695830808081938623 2775005543746212122907935)
        ·
          refine ⟨4162508315619318184361903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2775005543746212122907935 4162508315619318184361903)
          ·
            refine ⟨6243762473428977276542855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162508315619318184361903 6243762473428977276542855)
            ·
              refine ⟨9365643710143465914814283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6243762473428977276542855 9365643710143465914814283)
              ·
                refine ⟨14048465565215198872221425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9365643710143465914814283 14048465565215198872221425)
                ·
                  refine ⟨10536349173911399154166069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14048465565215198872221425 10536349173911399154166069)
                  ·
                    refine ⟨987782735054193670703069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10536349173911399154166069 987782735054193670703069)
                    ·
                      rfl

theorem cell22_2885550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_2885550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885550 prefixEnd_2885550 := by exact prefixLift 2885550
  have htrace : WordTrace (prefixWord ++ tailWord_2885550) baseStart_2885550 baseEnd_2885550 := by
    simpa [prefixWord, tailWord_2885550, baseEnd_2885550] using wordTrace_append hprefix tailTrace_2885550
  have hstable : (prefixWord ++ tailWord_2885550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885550).length < 2 ^ (prefixWord ++ tailWord_2885550).sum := by decide
  have hdescent : baseEnd_2885550 < baseStart_2885550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885561 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 2, 3]
def baseStart_2885561 : Nat := 118140960795 + 2885561 * 2 ^ 59
def prefixEnd_2885561 : Nat := 4983230072969 + 3 ^ 40 * 2885561 * 2
def baseEnd_2885561 : Nat := 987786500578993308678035

theorem tailTrace_2885561 : CollatzResearch.WordTrace tailWord_2885561 prefixEnd_2885561 987786500578993308678035 := by
  unfold tailWord_2885561
  simp only [CollatzResearch.WordTrace]
  refine ⟨105245055899112786428936537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70163370599408524285957691 105245055899112786428936537)
  ·
    refine ⟨78933791924334589821702403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105245055899112786428936537 78933791924334589821702403)
    ·
      refine ⟨118400687886501884732553605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78933791924334589821702403 118400687886501884732553605)
      ·
        refine ⟨22200128978719103387353801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118400687886501884732553605 22200128978719103387353801)
        ·
          refine ⟨16650096734039327540515351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22200128978719103387353801 16650096734039327540515351)
          ·
            refine ⟨24975145101058991310773027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16650096734039327540515351 24975145101058991310773027)
            ·
              refine ⟨37462717651588486966159541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24975145101058991310773027 37462717651588486966159541)
              ·
                refine ⟨3512129779836420653077457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37462717651588486966159541 3512129779836420653077457)
                ·
                  refine ⟨2634097334877315489808093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3512129779836420653077457 2634097334877315489808093)
                  ·
                    refine ⟨987786500578993308678035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2634097334877315489808093 987786500578993308678035)
                    ·
                      rfl

theorem cell22_2885561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 2, 3].length) (baseStart_2885561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885561 prefixEnd_2885561 := by exact prefixLift 2885561
  have htrace : WordTrace (prefixWord ++ tailWord_2885561) baseStart_2885561 baseEnd_2885561 := by
    simpa [prefixWord, tailWord_2885561, baseEnd_2885561] using wordTrace_append hprefix tailTrace_2885561
  have hstable : (prefixWord ++ tailWord_2885561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885561).length < 2 ^ (prefixWord ++ tailWord_2885561).sum := by decide
  have hdescent : baseEnd_2885561 < baseStart_2885561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885576 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 2, 4]
def baseStart_2885576 : Nat := 118140960795 + 2885576 * 2 ^ 59
def prefixEnd_2885576 : Nat := 4983230072969 + 3 ^ 40 * 2885576 * 2
def baseEnd_2885576 : Nat := 987791635385538269552989

theorem tailTrace_2885576 : CollatzResearch.WordTrace tailWord_2885576 prefixEnd_2885576 987791635385538269552989 := by
  unfold tailWord_2885576
  simp only [CollatzResearch.WordTrace]
  refine ⟨52622801497029221995366291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70163735329372295993821721 52622801497029221995366291)
  ·
    refine ⟨78934202245543832993049437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52622801497029221995366291 78934202245543832993049437)
    ·
      refine ⟨29600325842078937372393539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78934202245543832993049437 29600325842078937372393539)
      ·
        refine ⟨44400488763118406058590309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29600325842078937372393539 44400488763118406058590309)
        ·
          refine ⟨8325091643084701135985683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44400488763118406058590309 8325091643084701135985683)
          ·
            refine ⟨12487637464627051703978525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8325091643084701135985683 12487637464627051703978525)
            ·
              refine ⟨4682864049235144388991947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12487637464627051703978525 4682864049235144388991947)
              ·
                refine ⟨7024296073852716583487921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4682864049235144388991947 7024296073852716583487921)
                ·
                  refine ⟨5268222055389537437615941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7024296073852716583487921 5268222055389537437615941)
                  ·
                    refine ⟨987791635385538269552989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5268222055389537437615941 987791635385538269552989)
                    ·
                      rfl

theorem cell22_2885576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_2885576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885576 prefixEnd_2885576 := by exact prefixLift 2885576
  have htrace : WordTrace (prefixWord ++ tailWord_2885576) baseStart_2885576 baseEnd_2885576 := by
    simpa [prefixWord, tailWord_2885576, baseEnd_2885576] using wordTrace_append hprefix tailTrace_2885576
  have hstable : (prefixWord ++ tailWord_2885576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885576).length < 2 ^ (prefixWord ++ tailWord_2885576).sum := by decide
  have hdescent : baseEnd_2885576 < baseStart_2885576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885619 : List Nat := [1, 1, 1, 2, 2, 2, 1, 7, 5]
def baseStart_2885619 : Nat := 118140960795 + 2885619 * 2 ^ 59
def prefixEnd_2885619 : Nat := 4983230072969 + 3 ^ 40 * 2885619 * 2
def baseEnd_2885619 : Nat := 329268785054766830242619

theorem tailTrace_2885619 : CollatzResearch.WordTrace tailWord_2885619 prefixEnd_2885619 329268785054766830242619 := by
  unfold tailWord_2885619
  simp only [CollatzResearch.WordTrace]
  refine ⟨105247171332902662334547911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70164780888601774889698607 105247171332902662334547911)
  ·
    refine ⟨157870756999353993501821867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105247171332902662334547911 157870756999353993501821867)
    ·
      refine ⟨236806135499030990252732801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157870756999353993501821867 236806135499030990252732801)
      ·
        refine ⟨177604601624273242689549601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236806135499030990252732801 177604601624273242689549601)
        ·
          refine ⟨133203451218204932017162201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177604601624273242689549601 133203451218204932017162201)
          ·
            refine ⟨99902588413653699012871651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133203451218204932017162201 99902588413653699012871651)
            ·
              refine ⟨149853882620480548519307477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99902588413653699012871651 149853882620480548519307477)
              ·
                refine ⟨3512200373917512855921269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 149853882620480548519307477 3512200373917512855921269)
                ·
                  refine ⟨329268785054766830242619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3512200373917512855921269 329268785054766830242619)
                  ·
                    rfl

theorem cell22_2885619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 7, 5].length) (baseStart_2885619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885619 prefixEnd_2885619 := by exact prefixLift 2885619
  have htrace : WordTrace (prefixWord ++ tailWord_2885619) baseStart_2885619 baseEnd_2885619 := by
    simpa [prefixWord, tailWord_2885619, baseEnd_2885619] using wordTrace_append hprefix tailTrace_2885619
  have hstable : (prefixWord ++ tailWord_2885619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885619).length < 2 ^ (prefixWord ++ tailWord_2885619).sum := by decide
  have hdescent : baseEnd_2885619 < baseStart_2885619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885649 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 7, 4]
def baseStart_2885649 : Nat := 118140960795 + 2885649 * 2 ^ 59
def prefixEnd_2885649 : Nat := 4983230072969 + 3 ^ 40 * 2885649 * 2
def baseEnd_2885649 : Nat := 987816624777390412477765

theorem tailTrace_2885649 : CollatzResearch.WordTrace tailWord_2885649 prefixEnd_2885649 987816624777390412477765 := by
  unfold tailWord_2885649
  simp only [CollatzResearch.WordTrace]
  refine ⟨105248265522793977458140001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70165510348529318305426667 105248265522793977458140001)
  ·
    refine ⟨78936199142095483093605001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105248265522793977458140001 78936199142095483093605001)
    ·
      refine ⟨59202149356571612320203751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78936199142095483093605001 59202149356571612320203751)
      ·
        refine ⟨88803224034857418480305627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59202149356571612320203751 88803224034857418480305627)
        ·
          refine ⟨133204836052286127720458441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88803224034857418480305627 133204836052286127720458441)
          ·
            refine ⟨99903627039214595790343831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133204836052286127720458441 99903627039214595790343831)
            ·
              refine ⟨149855440558821893685515747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99903627039214595790343831 149855440558821893685515747)
              ·
                refine ⟨224783160838232840528273621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 149855440558821893685515747 224783160838232840528273621)
                ·
                  refine ⟨5268355332146082199881413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 224783160838232840528273621 5268355332146082199881413)
                  ·
                    refine ⟨987816624777390412477765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5268355332146082199881413 987816624777390412477765)
                    ·
                      rfl

theorem cell22_2885649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 4].length) (baseStart_2885649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885649 prefixEnd_2885649 := by exact prefixLift 2885649
  have htrace : WordTrace (prefixWord ++ tailWord_2885649) baseStart_2885649 baseEnd_2885649 := by
    simpa [prefixWord, tailWord_2885649, baseEnd_2885649] using wordTrace_append hprefix tailTrace_2885649
  have hstable : (prefixWord ++ tailWord_2885649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885649).length < 2 ^ (prefixWord ++ tailWord_2885649).sum := by decide
  have hdescent : baseEnd_2885649 < baseStart_2885649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885666 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 3, 4]
def baseStart_2885666 : Nat := 118140960795 + 2885666 * 2 ^ 59
def prefixEnd_2885666 : Nat := 4983230072969 + 3 ^ 40 * 2885666 * 2
def baseEnd_2885666 : Nat := 987822444224808034802713

theorem tailTrace_2885666 : CollatzResearch.WordTrace tailWord_2885666 prefixEnd_2885666 987822444224808034802713 := by
  unfold tailWord_2885666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26312221390933097340377213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70165923709154926241005901 26312221390933097340377213)
  ·
    refine ⟨9867083021599911502641455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26312221390933097340377213 9867083021599911502641455)
    ·
      refine ⟨14800624532399867253962183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9867083021599911502641455 14800624532399867253962183)
      ·
        refine ⟨22200936798599800880943275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14800624532399867253962183 22200936798599800880943275)
        ·
          refine ⟨33301405197899701321414913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22200936798599800880943275 33301405197899701321414913)
          ·
            refine ⟨24976053898424775991061185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33301405197899701321414913 24976053898424775991061185)
            ·
              refine ⟨18732040423818581993295889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24976053898424775991061185 18732040423818581993295889)
              ·
                refine ⟨14049030317863936494971917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18732040423818581993295889 14049030317863936494971917)
                ·
                  refine ⟨5268386369198976185614469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14049030317863936494971917 5268386369198976185614469)
                  ·
                    refine ⟨987822444224808034802713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5268386369198976185614469 987822444224808034802713)
                    ·
                      rfl

theorem cell22_2885666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_2885666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885666 prefixEnd_2885666 := by exact prefixLift 2885666
  have htrace : WordTrace (prefixWord ++ tailWord_2885666) baseStart_2885666 baseEnd_2885666 := by
    simpa [prefixWord, tailWord_2885666, baseEnd_2885666] using wordTrace_append hprefix tailTrace_2885666
  have hstable : (prefixWord ++ tailWord_2885666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885666).length < 2 ^ (prefixWord ++ tailWord_2885666).sum := by decide
  have hdescent : baseEnd_2885666 < baseStart_2885666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885696 : List Nat := [2, 1, 1, 2, 2, 5, 1, 2, 1, 5]
def baseStart_2885696 : Nat := 118140960795 + 2885696 * 2 ^ 59
def prefixEnd_2885696 : Nat := 4983230072969 + 3 ^ 40 * 2885696 * 2
def baseEnd_2885696 : Nat := 987832713837897956552621

theorem tailTrace_2885696 : CollatzResearch.WordTrace tailWord_2885696 prefixEnd_2885696 987832713837897956552621 := by
  unfold tailWord_2885696
  simp only [CollatzResearch.WordTrace]
  refine ⟨52624989876811852242550471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70166653169082469656733961 52624989876811852242550471)
  ·
    refine ⟨78937484815217778363825707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52624989876811852242550471 78937484815217778363825707)
    ·
      refine ⟨118406227222826667545738561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78937484815217778363825707 118406227222826667545738561)
      ·
        refine ⟨88804670417120000659303921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118406227222826667545738561 88804670417120000659303921)
        ·
          refine ⟨66603502812840000494477941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88804670417120000659303921 66603502812840000494477941)
          ·
            refine ⟨6244078388703750046357307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66603502812840000494477941 6244078388703750046357307)
            ·
              refine ⟨9366117583055625069535961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6244078388703750046357307 9366117583055625069535961)
              ·
                refine ⟨7024588187291718802151971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9366117583055625069535961 7024588187291718802151971)
                ·
                  refine ⟨10536882280937578203227957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7024588187291718802151971 10536882280937578203227957)
                  ·
                    refine ⟨987832713837897956552621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10536882280937578203227957 987832713837897956552621)
                    ·
                      rfl

theorem cell22_2885696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 5, 1, 2, 1, 5].length) (baseStart_2885696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885696 prefixEnd_2885696 := by exact prefixLift 2885696
  have htrace : WordTrace (prefixWord ++ tailWord_2885696) baseStart_2885696 baseEnd_2885696 := by
    simpa [prefixWord, tailWord_2885696, baseEnd_2885696] using wordTrace_append hprefix tailTrace_2885696
  have hstable : (prefixWord ++ tailWord_2885696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885696).length < 2 ^ (prefixWord ++ tailWord_2885696).sum := by decide
  have hdescent : baseEnd_2885696 < baseStart_2885696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885730 : List Nat := [3, 3, 2, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2885730 : Nat := 118140960795 + 2885730 * 2 ^ 59
def prefixEnd_2885730 : Nat := 4983230072969 + 3 ^ 40 * 2885730 * 2
def baseEnd_2885730 : Nat := 987844352732733201202517

theorem tailTrace_2885730 : CollatzResearch.WordTrace tailWord_2885730 prefixEnd_2885730 987844352732733201202517 := by
  unfold tailWord_2885730
  simp only [CollatzResearch.WordTrace]
  refine ⟨26312804958875132072959661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70167479890333685527892429 26312804958875132072959661)
  ·
    refine ⟨9867301859578174527359873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26312804958875132072959661 9867301859578174527359873)
    ·
      refine ⟨7400476394683630895519905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9867301859578174527359873 7400476394683630895519905)
      ·
        refine ⟨5550357296012723171639929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7400476394683630895519905 5550357296012723171639929)
        ·
          refine ⟨4162767972009542378729947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5550357296012723171639929 4162767972009542378729947)
          ·
            refine ⟨6244151958014313568094921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162767972009542378729947 6244151958014313568094921)
            ·
              refine ⟨4683113968510735176071191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6244151958014313568094921 4683113968510735176071191)
              ·
                refine ⟨7024670952766102764106787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4683113968510735176071191 7024670952766102764106787)
                ·
                  refine ⟨10537006429149154146160181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7024670952766102764106787 10537006429149154146160181)
                  ·
                    refine ⟨987844352732733201202517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10537006429149154146160181 987844352732733201202517)
                    ·
                      rfl

theorem cell22_2885730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2885730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885730 prefixEnd_2885730 := by exact prefixLift 2885730
  have htrace : WordTrace (prefixWord ++ tailWord_2885730) baseStart_2885730 baseEnd_2885730 := by
    simpa [prefixWord, tailWord_2885730, baseEnd_2885730] using wordTrace_append hprefix tailTrace_2885730
  have hstable : (prefixWord ++ tailWord_2885730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885730).length < 2 ^ (prefixWord ++ tailWord_2885730).sum := by decide
  have hdescent : baseEnd_2885730 < baseStart_2885730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885809 : List Nat := [1, 2, 2, 5, 2, 2, 1, 3, 1, 3]
def baseStart_2885809 : Nat := 118140960795 + 2885809 * 2 ^ 59
def prefixEnd_2885809 : Nat := 4983230072969 + 3 ^ 40 * 2885809 * 2
def baseEnd_2885809 : Nat := 987871396047203328477275

theorem tailTrace_2885809 : CollatzResearch.WordTrace tailWord_2885809 prefixEnd_2885809 987871396047203328477275 := by
  unfold tailWord_2885809
  simp only [CollatzResearch.WordTrace]
  refine ⟨105254101202214324783964481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70169400801476216522642987 105254101202214324783964481)
  ·
    refine ⟨78940575901660743587973361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105254101202214324783964481 78940575901660743587973361)
    ·
      refine ⟨59205431926245557690980021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78940575901660743587973361 59205431926245557690980021)
      ·
        refine ⟨5550509243085521033529377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59205431926245557690980021 5550509243085521033529377)
        ·
          refine ⟨4162881932314140775147033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5550509243085521033529377 4162881932314140775147033)
          ·
            refine ⟨3122161449235605581360275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4162881932314140775147033 3122161449235605581360275)
            ·
              refine ⟨4683242173853408372040413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3122161449235605581360275 4683242173853408372040413)
              ·
                refine ⟨1756215815195028139515155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4683242173853408372040413 1756215815195028139515155)
                ·
                  refine ⟨2634323722792542209272733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756215815195028139515155 2634323722792542209272733)
                  ·
                    refine ⟨987871396047203328477275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2634323722792542209272733 987871396047203328477275)
                    ·
                      rfl

theorem cell22_2885809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 1, 3].length) (baseStart_2885809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885809 prefixEnd_2885809 := by exact prefixLift 2885809
  have htrace : WordTrace (prefixWord ++ tailWord_2885809) baseStart_2885809 baseEnd_2885809 := by
    simpa [prefixWord, tailWord_2885809, baseEnd_2885809] using wordTrace_append hprefix tailTrace_2885809
  have hstable : (prefixWord ++ tailWord_2885809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885809).length < 2 ^ (prefixWord ++ tailWord_2885809).sum := by decide
  have hdescent : baseEnd_2885809 < baseStart_2885809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885818 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 1, 4]
def baseStart_2885818 : Nat := 118140960795 + 2885818 * 2 ^ 59
def prefixEnd_2885818 : Nat := 4983230072969 + 3 ^ 40 * 2885818 * 2
def baseEnd_2885818 : Nat := 987874476931130305002247

theorem tailTrace_2885818 : CollatzResearch.WordTrace tailWord_2885818 prefixEnd_2885818 987874476931130305002247 := by
  unfold tailWord_2885818
  simp only [CollatzResearch.WordTrace]
  refine ⟨26313607364795429830260527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70169619639454479547361405 26313607364795429830260527)
  ·
    refine ⟨39470411047193144745390791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26313607364795429830260527 39470411047193144745390791)
    ·
      refine ⟨59205616570789717118086187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39470411047193144745390791 59205616570789717118086187)
      ·
        refine ⟨88808424856184575677129281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59205616570789717118086187 88808424856184575677129281)
        ·
          refine ⟨66606318642138431757846961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88808424856184575677129281 66606318642138431757846961)
          ·
            refine ⟨49954738981603823818385221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66606318642138431757846961 49954738981603823818385221)
            ·
              refine ⟨9366513559050716965947229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49954738981603823818385221 9366513559050716965947229)
              ·
                refine ⟨3512442584644018862230211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9366513559050716965947229 3512442584644018862230211)
                ·
                  refine ⟨5268663876966028293345317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512442584644018862230211 5268663876966028293345317)
                  ·
                    refine ⟨987874476931130305002247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5268663876966028293345317 987874476931130305002247)
                    ·
                      rfl

theorem cell22_2885818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 4].length) (baseStart_2885818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885818 prefixEnd_2885818 := by exact prefixLift 2885818
  have htrace : WordTrace (prefixWord ++ tailWord_2885818) baseStart_2885818 baseEnd_2885818 := by
    simpa [prefixWord, tailWord_2885818, baseEnd_2885818] using wordTrace_append hprefix tailTrace_2885818
  have hstable : (prefixWord ++ tailWord_2885818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885818).length < 2 ^ (prefixWord ++ tailWord_2885818).sum := by decide
  have hdescent : baseEnd_2885818 < baseStart_2885818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885852 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 3, 4]
def baseStart_2885852 : Nat := 118140960795 + 2885852 * 2 ^ 59
def prefixEnd_2885852 : Nat := 4983230072969 + 3 ^ 40 * 2885852 * 2
def baseEnd_2885852 : Nat := 987886115825965549652143

theorem tailTrace_2885852 : CollatzResearch.WordTrace tailWord_2885852 prefixEnd_2885852 987886115825965549652143 := by
  unfold tailWord_2885852
  simp only [CollatzResearch.WordTrace]
  refine ⟨52627834770529271563889905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70170446360705695418519873 52627834770529271563889905)
  ·
    refine ⟨39470876077896953672917429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52627834770529271563889905 39470876077896953672917429)
    ·
      refine ⟨3700394632302839406836009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39470876077896953672917429 3700394632302839406836009)
      ·
        refine ⟨2775295974227129555127007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3700394632302839406836009 2775295974227129555127007)
        ·
          refine ⟨4162943961340694332690511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2775295974227129555127007 4162943961340694332690511)
          ·
            refine ⟨6244415942011041499035767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4162943961340694332690511 6244415942011041499035767)
            ·
              refine ⟨9366623913016562248553651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6244415942011041499035767 9366623913016562248553651)
              ·
                refine ⟨14049935869524843372830477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9366623913016562248553651 14049935869524843372830477)
                ·
                  refine ⟨5268725951071816264811429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14049935869524843372830477 5268725951071816264811429)
                  ·
                    refine ⟨987886115825965549652143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5268725951071816264811429 987886115825965549652143)
                    ·
                      rfl

theorem cell22_2885852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_2885852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885852 prefixEnd_2885852 := by exact prefixLift 2885852
  have htrace : WordTrace (prefixWord ++ tailWord_2885852) baseStart_2885852 baseEnd_2885852 := by
    simpa [prefixWord, tailWord_2885852, baseEnd_2885852] using wordTrace_append hprefix tailTrace_2885852
  have hstable : (prefixWord ++ tailWord_2885852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885852).length < 2 ^ (prefixWord ++ tailWord_2885852).sum := by decide
  have hdescent : baseEnd_2885852 < baseStart_2885852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885891 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 1, 8]
def baseStart_2885891 : Nat := 118140960795 + 2885891 * 2 ^ 59
def prefixEnd_2885891 : Nat := 4983230072969 + 3 ^ 40 * 2885891 * 2
def baseEnd_2885891 : Nat := 987899466322982447927023

theorem tailTrace_2885891 : CollatzResearch.WordTrace tailWord_2885891 prefixEnd_2885891 987899466322982447927023 := by
  unfold tailWord_2885891
  simp only [CollatzResearch.WordTrace]
  refine ⟨105257091987917252788449527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70171394658611501858966351 105257091987917252788449527)
  ·
    refine ⟨157885637981875879182674291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105257091987917252788449527 157885637981875879182674291)
    ·
      refine ⟨236828456972813818774011437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157885637981875879182674291 236828456972813818774011437)
      ·
        refine ⟨88810671364805182040254289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 236828456972813818774011437 88810671364805182040254289)
        ·
          refine ⟨66608003523603886530190717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88810671364805182040254289 66608003523603886530190717)
          ·
            refine ⟨24978001321351457448821519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66608003523603886530190717 24978001321351457448821519)
            ·
              refine ⟨37467001982027186173232279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24978001321351457448821519 37467001982027186173232279)
              ·
                refine ⟨56200502973040779259848419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37467001982027186173232279 56200502973040779259848419)
                ·
                  refine ⟨84300754459561168889772629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56200502973040779259848419 84300754459561168889772629)
                  ·
                    refine ⟨987899466322982447927023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84300754459561168889772629 987899466322982447927023)
                    ·
                      rfl

theorem cell22_2885891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 8].length) (baseStart_2885891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885891 prefixEnd_2885891 := by exact prefixLift 2885891
  have htrace : WordTrace (prefixWord ++ tailWord_2885891) baseStart_2885891 baseEnd_2885891 := by
    simpa [prefixWord, tailWord_2885891, baseEnd_2885891] using wordTrace_append hprefix tailTrace_2885891
  have hstable : (prefixWord ++ tailWord_2885891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885891).length < 2 ^ (prefixWord ++ tailWord_2885891).sum := by decide
  have hdescent : baseEnd_2885891 < baseStart_2885891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885940 : List Nat := [2, 5, 1, 1, 1, 3, 1, 1, 7]
def baseStart_2885940 : Nat := 118140960795 + 2885940 * 2 ^ 59
def prefixEnd_2885940 : Nat := 4983230072969 + 3 ^ 40 * 2885940 * 2
def baseEnd_2885940 : Nat := 329305413341454217817291

theorem tailTrace_2885940 : CollatzResearch.WordTrace tailWord_2885940 prefixEnd_2885940 329305413341454217817291 := by
  unfold tailWord_2885940
  simp only [CollatzResearch.WordTrace]
  refine ⟨52629439582369867078491637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70172586109826489437988849 52629439582369867078491637)
  ·
    refine ⟨4934009960847175038608591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52629439582369867078491637 4934009960847175038608591)
    ·
      refine ⟨7401014941270762557912887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4934009960847175038608591 7401014941270762557912887)
      ·
        refine ⟨11101522411906143836869331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7401014941270762557912887 11101522411906143836869331)
        ·
          refine ⟨16652283617859215755303997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11101522411906143836869331 16652283617859215755303997)
          ·
            refine ⟨6244606356697205908238999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16652283617859215755303997 6244606356697205908238999)
            ·
              refine ⟨9366909535045808862358499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6244606356697205908238999 9366909535045808862358499)
              ·
                refine ⟨14050364302568713293537749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9366909535045808862358499 14050364302568713293537749)
                ·
                  refine ⟨329305413341454217817291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14050364302568713293537749 329305413341454217817291)
                  ·
                    rfl

theorem cell22_2885940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_2885940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885940 prefixEnd_2885940 := by exact prefixLift 2885940
  have htrace : WordTrace (prefixWord ++ tailWord_2885940) baseStart_2885940 baseEnd_2885940 := by
    simpa [prefixWord, tailWord_2885940, baseEnd_2885940] using wordTrace_append hprefix tailTrace_2885940
  have hstable : (prefixWord ++ tailWord_2885940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885940).length < 2 ^ (prefixWord ++ tailWord_2885940).sum := by decide
  have hdescent : baseEnd_2885940 < baseStart_2885940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885968 : List Nat := [2, 1, 1, 1, 1, 6, 2, 2, 6]
def baseStart_2885968 : Nat := 118140960795 + 2885968 * 2 ^ 59
def prefixEnd_2885968 : Nat := 4983230072969 + 3 ^ 40 * 2885968 * 2
def baseEnd_2885968 : Nat := 329308608332193304583929

theorem tailTrace_2885968 : CollatzResearch.WordTrace tailWord_2885968 prefixEnd_2885968 329308608332193304583929 := by
  unfold tailWord_2885968
  simp only [CollatzResearch.WordTrace]
  refine ⟨52629950204319147469501279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70173266939092196626001705 52629950204319147469501279)
  ·
    refine ⟨78944925306478721204251919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52629950204319147469501279 78944925306478721204251919)
    ·
      refine ⟨118417387959718081806377879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78944925306478721204251919 118417387959718081806377879)
      ·
        refine ⟨177626081939577122709566819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118417387959718081806377879 177626081939577122709566819)
        ·
          refine ⟨266439122909365684064350229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177626081939577122709566819 266439122909365684064350229)
          ·
            refine ⟨12489333886376516440516417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 266439122909365684064350229 12489333886376516440516417)
            ·
              refine ⟨9367000414782387330387313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12489333886376516440516417 9367000414782387330387313)
              ·
                refine ⟨7025250311086790497790485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9367000414782387330387313 7025250311086790497790485)
                ·
                  refine ⟨329308608332193304583929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7025250311086790497790485 329308608332193304583929)
                  ·
                    rfl

theorem cell22_2885968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 2, 2, 6].length) (baseStart_2885968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885968 prefixEnd_2885968 := by exact prefixLift 2885968
  have htrace : WordTrace (prefixWord ++ tailWord_2885968) baseStart_2885968 baseEnd_2885968 := by
    simpa [prefixWord, tailWord_2885968, baseEnd_2885968] using wordTrace_append hprefix tailTrace_2885968
  have hstable : (prefixWord ++ tailWord_2885968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885968).length < 2 ^ (prefixWord ++ tailWord_2885968).sum := by decide
  have hdescent : baseEnd_2885968 < baseStart_2885968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885970 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 1, 4]
def baseStart_2885970 : Nat := 118140960795 + 2885970 * 2 ^ 59
def prefixEnd_2885970 : Nat := 4983230072969 + 3 ^ 40 * 2885970 * 2
def baseEnd_2885970 : Nat := 987926509637452575201781

theorem tailTrace_2885970 : CollatzResearch.WordTrace tailWord_2885970 prefixEnd_2885970 987926509637452575201781 := by
  unfold tailWord_2885970
  simp only [CollatzResearch.WordTrace]
  refine ⟨26314993338657762320143841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70173315569754032853716909 26314993338657762320143841)
  ·
    refine ⟨19736245003993321740107881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26314993338657762320143841 19736245003993321740107881)
    ·
      refine ⟨14802183752994991305080911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19736245003993321740107881 14802183752994991305080911)
      ·
        refine ⟨22203275629492486957621367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14802183752994991305080911 22203275629492486957621367)
        ·
          refine ⟨33304913444238730436432051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22203275629492486957621367 33304913444238730436432051)
          ·
            refine ⟨49957370166358095654648077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33304913444238730436432051 49957370166358095654648077)
            ·
              refine ⟨18734013812384285870493029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49957370166358095654648077 18734013812384285870493029)
              ·
                refine ⟨3512627589822053600717443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18734013812384285870493029 3512627589822053600717443)
                ·
                  refine ⟨5268941384733080401076165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512627589822053600717443 5268941384733080401076165)
                  ·
                    refine ⟨987926509637452575201781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5268941384733080401076165 987926509637452575201781)
                    ·
                      rfl

theorem cell22_2885970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_2885970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885970 prefixEnd_2885970 := by exact prefixLift 2885970
  have htrace : WordTrace (prefixWord ++ tailWord_2885970) baseStart_2885970 baseEnd_2885970 := by
    simpa [prefixWord, tailWord_2885970, baseEnd_2885970] using wordTrace_append hprefix tailTrace_2885970
  have hstable : (prefixWord ++ tailWord_2885970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885970).length < 2 ^ (prefixWord ++ tailWord_2885970).sum := by decide
  have hdescent : baseEnd_2885970 < baseStart_2885970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2885983 : List Nat := [1, 1, 2, 3, 1, 2, 2, 4, 1, 5]
def baseStart_2885983 : Nat := 118140960795 + 2885983 * 2 ^ 59
def prefixEnd_2885983 : Nat := 4983230072969 + 3 ^ 40 * 2885983 * 2
def baseEnd_2885983 : Nat := 987930959803124874626741

theorem tailTrace_2885983 : CollatzResearch.WordTrace tailWord_2885983 prefixEnd_2885983 987930959803124874626741 := by
  unfold tailWord_2885983
  simp only [CollatzResearch.WordTrace]
  refine ⟨105260447503583952500798603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70173631669055968333865735 105260447503583952500798603)
  ·
    refine ⟨157890671255375928751197905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105260447503583952500798603 157890671255375928751197905)
    ·
      refine ⟨118418003441531946563398429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157890671255375928751197905 118418003441531946563398429)
      ·
        refine ⟨44406751290574479961274411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118418003441531946563398429 44406751290574479961274411)
        ·
          refine ⟨66610126935861719941911617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44406751290574479961274411 66610126935861719941911617)
          ·
            refine ⟨49957595201896289956433713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66610126935861719941911617 49957595201896289956433713)
            ·
              refine ⟨37468196401422217467325285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49957595201896289956433713 37468196401422217467325285)
              ·
                refine ⟨7025286825266665775123491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37468196401422217467325285 7025286825266665775123491)
                ·
                  refine ⟨10537930237899998662685237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7025286825266665775123491 10537930237899998662685237)
                  ·
                    refine ⟨987930959803124874626741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10537930237899998662685237 987930959803124874626741)
                    ·
                      rfl

theorem cell22_2885983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_2885983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2885983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2885983 prefixEnd_2885983 := by exact prefixLift 2885983
  have htrace : WordTrace (prefixWord ++ tailWord_2885983) baseStart_2885983 baseEnd_2885983 := by
    simpa [prefixWord, tailWord_2885983, baseEnd_2885983] using wordTrace_append hprefix tailTrace_2885983
  have hstable : (prefixWord ++ tailWord_2885983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2885983).length < 2 ^ (prefixWord ++ tailWord_2885983).sum := by decide
  have hdescent : baseEnd_2885983 < baseStart_2885983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2885983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886000 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 4, 3]
def baseStart_2886000 : Nat := 118140960795 + 2886000 * 2 ^ 59
def prefixEnd_2886000 : Nat := 4983230072969 + 3 ^ 40 * 2886000 * 2
def baseEnd_2886000 : Nat := 987936779250542496951689

theorem tailTrace_2886000 : CollatzResearch.WordTrace tailWord_2886000 prefixEnd_2886000 987936779250542496951689 := by
  unfold tailWord_2886000
  simp only [CollatzResearch.WordTrace]
  refine ⟨52630533772261182202083727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70174045029681576269444969 52630533772261182202083727)
  ·
    refine ⟨78945800658391773303125591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52630533772261182202083727 78945800658391773303125591)
    ·
      refine ⟨118418700987587659954688387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78945800658391773303125591 118418700987587659954688387)
      ·
        refine ⟨177628051481381489932032581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118418700987587659954688387 177628051481381489932032581)
        ·
          refine ⟨33305259652759029362256109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177628051481381489932032581 33305259652759029362256109)
          ·
            refine ⟨12489472369784636010846041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33305259652759029362256109 12489472369784636010846041)
            ·
              refine ⟨9367104277338477008134531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12489472369784636010846041 9367104277338477008134531)
              ·
                refine ⟨14050656416007715512201797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9367104277338477008134531 14050656416007715512201797)
                ·
                  refine ⟨2634498078001446658537837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14050656416007715512201797 2634498078001446658537837)
                  ·
                    refine ⟨987936779250542496951689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2634498078001446658537837 987936779250542496951689)
                    ·
                      rfl

theorem cell22_2886000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 4, 3].length) (baseStart_2886000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886000 prefixEnd_2886000 := by exact prefixLift 2886000
  have htrace : WordTrace (prefixWord ++ tailWord_2886000) baseStart_2886000 baseEnd_2886000 := by
    simpa [prefixWord, tailWord_2886000, baseEnd_2886000] using wordTrace_append hprefix tailTrace_2886000
  have hstable : (prefixWord ++ tailWord_2886000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886000).length < 2 ^ (prefixWord ++ tailWord_2886000).sum := by decide
  have hdescent : baseEnd_2886000 < baseStart_2886000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886013 : List Nat := [1, 4, 1, 1, 2, 3, 1, 9]
def baseStart_2886013 : Nat := 118140960795 + 2886013 * 2 ^ 59
def prefixEnd_2886013 : Nat := 4983230072969 + 3 ^ 40 * 2886013 * 2
def baseEnd_2886013 : Nat := 109771247712912755152961

theorem tailTrace_2886013 : CollatzResearch.WordTrace tailWord_2886013 prefixEnd_2886013 109771247712912755152961 := by
  unfold tailWord_2886013
  simp only [CollatzResearch.WordTrace]
  refine ⟨105261541693475267624390693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70174361128983511749593795 105261541693475267624390693)
  ·
    refine ⟨19736539067526612679573255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105261541693475267624390693 19736539067526612679573255)
    ·
      refine ⟨29604808601289919019359883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19736539067526612679573255 29604808601289919019359883)
      ·
        refine ⟨44407212901934878529039825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29604808601289919019359883 44407212901934878529039825)
        ·
          refine ⟨33305409676451158896779869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44407212901934878529039825 33305409676451158896779869)
          ·
            refine ⟨12489528628669184586292451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33305409676451158896779869 12489528628669184586292451)
            ·
              refine ⟨18734292943003776879438677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12489528628669184586292451 18734292943003776879438677)
              ·
                refine ⟨109771247712912755152961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18734292943003776879438677 109771247712912755152961)
                ·
                  rfl

theorem cell22_2886013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 9].length) (baseStart_2886013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886013 prefixEnd_2886013 := by exact prefixLift 2886013
  have htrace : WordTrace (prefixWord ++ tailWord_2886013) baseStart_2886013 baseEnd_2886013 := by
    simpa [prefixWord, tailWord_2886013, baseEnd_2886013] using wordTrace_append hprefix tailTrace_2886013
  have hstable : (prefixWord ++ tailWord_2886013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886013).length < 2 ^ (prefixWord ++ tailWord_2886013).sum := by decide
  have hdescent : baseEnd_2886013 < baseStart_2886013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886030 : List Nat := [4, 1, 1, 4, 1, 1, 2, 8]
def baseStart_2886030 : Nat := 118140960795 + 2886030 * 2 ^ 59
def prefixEnd_2886030 : Nat := 4983230072969 + 3 ^ 40 * 2886030 * 2
def baseEnd_2886030 : Nat := 109771894318181379855733

theorem tailTrace_2886030 : CollatzResearch.WordTrace tailWord_2886030 prefixEnd_2886030 109771894318181379855733 := by
  unfold tailWord_2886030
  simp only [CollatzResearch.WordTrace]
  refine ⟨13157770216801709940969943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70174774489609119685173029 13157770216801709940969943)
  ·
    refine ⟨19736655325202564911454915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13157770216801709940969943 19736655325202564911454915)
    ·
      refine ⟨29604982987803847367182373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19736655325202564911454915 29604982987803847367182373)
      ·
        refine ⟨5550934310213221381346695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29604982987803847367182373 5550934310213221381346695)
        ·
          refine ⟨8326401465319832072020043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5550934310213221381346695 8326401465319832072020043)
          ·
            refine ⟨12489602197979748108030065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8326401465319832072020043 12489602197979748108030065)
            ·
              refine ⟨9367201648484811081022549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12489602197979748108030065 9367201648484811081022549)
              ·
                refine ⟨109771894318181379855733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9367201648484811081022549 109771894318181379855733)
                ·
                  rfl

theorem cell22_2886030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 8].length) (baseStart_2886030 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886030 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886030 prefixEnd_2886030 := by exact prefixLift 2886030
  have htrace : WordTrace (prefixWord ++ tailWord_2886030) baseStart_2886030 baseEnd_2886030 := by
    simpa [prefixWord, tailWord_2886030, baseEnd_2886030] using wordTrace_append hprefix tailTrace_2886030
  have hstable : (prefixWord ++ tailWord_2886030).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886030).length < 2 ^ (prefixWord ++ tailWord_2886030).sum := by decide
  have hdescent : baseEnd_2886030 < baseStart_2886030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886081 : List Nat := [1, 2, 7, 1, 1, 1, 3, 6]
def baseStart_2886081 : Nat := 118140960795 + 2886081 * 2 ^ 59
def prefixEnd_2886081 : Nat := 4983230072969 + 3 ^ 40 * 2886081 * 2
def baseEnd_2886081 : Nat := 109773834133987253964049

theorem tailTrace_2886081 : CollatzResearch.WordTrace tailWord_2886081 prefixEnd_2886081 109773834133987253964049 := by
  unfold tailWord_2886081
  simp only [CollatzResearch.WordTrace]
  refine ⟨105264021857228915237866097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70176014571485943491910731 105264021857228915237866097)
  ·
    refine ⟨78948016392921686428399573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105264021857228915237866097 78948016392921686428399573)
    ·
      refine ⟨1850344134209102025665615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 78948016392921686428399573 1850344134209102025665615)
      ·
        refine ⟨2775516201313653038498423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1850344134209102025665615 2775516201313653038498423)
        ·
          refine ⟨4163274301970479557747635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2775516201313653038498423 4163274301970479557747635)
          ·
            refine ⟨6244911452955719336621453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4163274301970479557747635 6244911452955719336621453)
            ·
              refine ⟨2341841794858394751233045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6244911452955719336621453 2341841794858394751233045)
              ·
                refine ⟨109773834133987253964049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2341841794858394751233045 109773834133987253964049)
                ·
                  rfl

theorem cell22_2886081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 6].length) (baseStart_2886081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886081 prefixEnd_2886081 := by exact prefixLift 2886081
  have htrace : WordTrace (prefixWord ++ tailWord_2886081) baseStart_2886081 baseEnd_2886081 := by
    simpa [prefixWord, tailWord_2886081, baseEnd_2886081] using wordTrace_append hprefix tailTrace_2886081
  have hstable : (prefixWord ++ tailWord_2886081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886081).length < 2 ^ (prefixWord ++ tailWord_2886081).sum := by decide
  have hdescent : baseEnd_2886081 < baseStart_2886081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886120 : List Nat := [2, 1, 4, 1, 1, 3, 1, 3, 6]
def baseStart_2886120 : Nat := 118140960795 + 2886120 * 2 ^ 59
def prefixEnd_2886120 : Nat := 4983230072969 + 3 ^ 40 * 2886120 * 2
def baseEnd_2886120 : Nat := 329325952567634061317107

theorem tailTrace_2886120 : CollatzResearch.WordTrace tailWord_2886120 prefixEnd_2886120 329325952567634061317107 := by
  unfold tailWord_2886120
  simp only [CollatzResearch.WordTrace]
  refine ⟨52632722152043812449267907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70176962869391749932357209 52632722152043812449267907)
  ·
    refine ⟨78949083228065718673901861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52632722152043812449267907 78949083228065718673901861)
    ·
      refine ⟨14802953105262322251356599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78949083228065718673901861 14802953105262322251356599)
      ·
        refine ⟨22204429657893483377034899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14802953105262322251356599 22204429657893483377034899)
        ·
          refine ⟨33306644486840225065552349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22204429657893483377034899 33306644486840225065552349)
          ·
            refine ⟨12489991682565084399582131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33306644486840225065552349 12489991682565084399582131)
            ·
              refine ⟨18734987523847626599373197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12489991682565084399582131 18734987523847626599373197)
              ·
                refine ⟨7025620321442859974764949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18734987523847626599373197 7025620321442859974764949)
                ·
                  refine ⟨329325952567634061317107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7025620321442859974764949 329325952567634061317107)
                  ·
                    rfl

theorem cell22_2886120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 1, 3, 6].length) (baseStart_2886120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886120 prefixEnd_2886120 := by exact prefixLift 2886120
  have htrace : WordTrace (prefixWord ++ tailWord_2886120) baseStart_2886120 baseEnd_2886120 := by
    simpa [prefixWord, tailWord_2886120, baseEnd_2886120] using wordTrace_append hprefix tailTrace_2886120
  have hstable : (prefixWord ++ tailWord_2886120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886120).length < 2 ^ (prefixWord ++ tailWord_2886120).sum := by decide
  have hdescent : baseEnd_2886120 < baseStart_2886120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886186 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 2, 3]
def baseStart_2886186 : Nat := 118140960795 + 2886186 * 2 ^ 59
def prefixEnd_2886186 : Nat := 4983230072969 + 3 ^ 40 * 2886186 * 2
def baseEnd_2886186 : Nat := 988000450851700011801119

theorem tailTrace_2886186 : CollatzResearch.WordTrace tailWord_2886186 prefixEnd_2886186 988000450851700011801119 := by
  unfold tailWord_2886186
  simp only [CollatzResearch.WordTrace]
  refine ⟨26316962880462129542609603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70178567681232345446958941 26316962880462129542609603)
  ·
    refine ⟨39475444320693194313914405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26316962880462129542609603 39475444320693194313914405)
    ·
      refine ⟨7401645810129973933858951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39475444320693194313914405 7401645810129973933858951)
      ·
        refine ⟨11102468715194960900788427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7401645810129973933858951 11102468715194960900788427)
        ·
          refine ⟨16653703072792441351182641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11102468715194960900788427 16653703072792441351182641)
          ·
            refine ⟨12490277304594331013386981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16653703072792441351182641 12490277304594331013386981)
            ·
              refine ⟨2341926994611437065010059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12490277304594331013386981 2341926994611437065010059)
              ·
                refine ⟨3512890491917155597515089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341926994611437065010059 3512890491917155597515089)
                ·
                  refine ⟨2634667868937866698136317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3512890491917155597515089 2634667868937866698136317)
                  ·
                    refine ⟨988000450851700011801119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2634667868937866698136317 988000450851700011801119)
                    ·
                      rfl

theorem cell22_2886186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_2886186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886186 prefixEnd_2886186 := by exact prefixLift 2886186
  have htrace : WordTrace (prefixWord ++ tailWord_2886186) baseStart_2886186 baseEnd_2886186 := by
    simpa [prefixWord, tailWord_2886186, baseEnd_2886186] using wordTrace_append hprefix tailTrace_2886186
  have hstable : (prefixWord ++ tailWord_2886186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886186).length < 2 ^ (prefixWord ++ tailWord_2886186).sum := by decide
  have hdescent : baseEnd_2886186 < baseStart_2886186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886197 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 5, 3]
def baseStart_2886197 : Nat := 118140960795 + 2886197 * 2 ^ 59
def prefixEnd_2886197 : Nat := 4983230072969 + 3 ^ 40 * 2886197 * 2
def baseEnd_2886197 : Nat := 988004216376499649776085

theorem tailTrace_2886197 : CollatzResearch.WordTrace tailWord_2886197 prefixEnd_2886197 988004216376499649776085 := by
  unfold tailWord_2886197
  simp only [CollatzResearch.WordTrace]
  refine ⟨105268252724808667049088845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70178835149872444699392563 105268252724808667049088845)
  ·
    refine ⟨39475594771803250143408317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105268252724808667049088845 39475594771803250143408317)
    ·
      refine ⟨14803348039426218803778119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39475594771803250143408317 14803348039426218803778119)
      ·
        refine ⟨22205022059139328205667179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14803348039426218803778119 22205022059139328205667179)
        ·
          refine ⟨33307533088708992308500769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22205022059139328205667179 33307533088708992308500769)
          ·
            refine ⟨24980649816531744231375577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33307533088708992308500769 24980649816531744231375577)
            ·
              refine ⟨18735487362398808173531683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24980649816531744231375577 18735487362398808173531683)
              ·
                refine ⟨28103231043598212260297525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18735487362398808173531683 28103231043598212260297525)
                ·
                  refine ⟨2634677910337332399402893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28103231043598212260297525 2634677910337332399402893)
                  ·
                    refine ⟨988004216376499649776085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2634677910337332399402893 988004216376499649776085)
                    ·
                      rfl

theorem cell22_2886197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_2886197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886197 prefixEnd_2886197 := by exact prefixLift 2886197
  have htrace : WordTrace (prefixWord ++ tailWord_2886197) baseStart_2886197 baseEnd_2886197 := by
    simpa [prefixWord, tailWord_2886197, baseEnd_2886197] using wordTrace_append hprefix tailTrace_2886197
  have hstable : (prefixWord ++ tailWord_2886197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886197).length < 2 ^ (prefixWord ++ tailWord_2886197).sum := by decide
  have hdescent : baseEnd_2886197 < baseStart_2886197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886255 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 8]
def baseStart_2886255 : Nat := 118140960795 + 2886255 * 2 ^ 59
def prefixEnd_2886255 : Nat := 4983230072969 + 3 ^ 40 * 2886255 * 2
def baseEnd_2886255 : Nat := 329341356987268943941969

theorem tailTrace_2886255 : CollatzResearch.WordTrace tailWord_2886255 prefixEnd_2886255 329341356987268943941969 := by
  unfold tailWord_2886255
  simp only [CollatzResearch.WordTrace]
  refine ⟨105270368158598542954700219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70180245439065695303133479 105270368158598542954700219)
  ·
    refine ⟨157905552237897814432050329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105270368158598542954700219 157905552237897814432050329)
    ·
      refine ⟨118429164178423360824037747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157905552237897814432050329 118429164178423360824037747)
      ·
        refine ⟨177643746267635041236056621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118429164178423360824037747 177643746267635041236056621)
        ·
          refine ⟨66616404850363140463521233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177643746267635041236056621 66616404850363140463521233)
          ·
            refine ⟨49962303637772355347640925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66616404850363140463521233 49962303637772355347640925)
            ·
              refine ⟨18735863864164633255365347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49962303637772355347640925 18735863864164633255365347)
              ·
                refine ⟨28103795796246949883048021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18735863864164633255365347 28103795796246949883048021)
                ·
                  refine ⟨329341356987268943941969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28103795796246949883048021 329341356987268943941969)
                  ·
                    rfl

theorem cell22_2886255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 8].length) (baseStart_2886255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886255 prefixEnd_2886255 := by exact prefixLift 2886255
  have htrace : WordTrace (prefixWord ++ tailWord_2886255) baseStart_2886255 baseEnd_2886255 := by
    simpa [prefixWord, tailWord_2886255, baseEnd_2886255] using wordTrace_append hprefix tailTrace_2886255
  have hstable : (prefixWord ++ tailWord_2886255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886255).length < 2 ^ (prefixWord ++ tailWord_2886255).sum := by decide
  have hdescent : baseEnd_2886255 < baseStart_2886255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886287 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 4, 3]
def baseStart_2886287 : Nat := 118140960795 + 2886287 * 2 ^ 59
def prefixEnd_2886287 : Nat := 4983230072969 + 3 ^ 40 * 2886287 * 2
def baseEnd_2886287 : Nat := 988035025215769415025809

theorem tailTrace_2886287 : CollatzResearch.WordTrace tailWord_2886287 prefixEnd_2886287 988035025215769415025809 := by
  unfold tailWord_2886287
  simp only [CollatzResearch.WordTrace]
  refine ⟨105271535294482612419865115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70181023529655074946576743 105271535294482612419865115)
  ·
    refine ⟨157907302941723918629797673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105271535294482612419865115 157907302941723918629797673)
    ·
      refine ⟨118430477206292938972348255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157907302941723918629797673 118430477206292938972348255)
      ·
        refine ⟨177645715809439408458522383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118430477206292938972348255 177645715809439408458522383)
        ·
          refine ⟨266468573714159112687783575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177645715809439408458522383 266468573714159112687783575)
          ·
            refine ⟨399702860571238669031675363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266468573714159112687783575 399702860571238669031675363)
            ·
              refine ⟨599554290856858003547513045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 399702860571238669031675363 599554290856858003547513045)
              ·
                refine ⟨14052053691957609458144837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 599554290856858003547513045 14052053691957609458144837)
                ·
                  refine ⟨2634760067242051773402157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14052053691957609458144837 2634760067242051773402157)
                  ·
                    refine ⟨988035025215769415025809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2634760067242051773402157 988035025215769415025809)
                    ·
                      rfl

theorem cell22_2886287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 4, 3].length) (baseStart_2886287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886287 prefixEnd_2886287 := by exact prefixLift 2886287
  have htrace : WordTrace (prefixWord ++ tailWord_2886287) baseStart_2886287 baseEnd_2886287 := by
    simpa [prefixWord, tailWord_2886287, baseEnd_2886287] using wordTrace_append hprefix tailTrace_2886287
  have hstable : (prefixWord ++ tailWord_2886287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886287).length < 2 ^ (prefixWord ++ tailWord_2886287).sum := by decide
  have hdescent : baseEnd_2886287 < baseStart_2886287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886473 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 2, 3]
def baseStart_2886473 : Nat := 118140960795 + 2886473 * 2 ^ 59
def prefixEnd_2886473 : Nat := 4983230072969 + 3 ^ 40 * 2886473 * 2
def baseEnd_2886473 : Nat := 988098696816926929875239

theorem tailTrace_2886473 : CollatzResearch.WordTrace tailWord_2886473 prefixEnd_2886473 988098696816926929875239 := by
  unfold tailWord_2886473
  simp only [CollatzResearch.WordTrace]
  refine ⟨105278319271808766186136073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70185546181205844124090715 105278319271808766186136073)
  ·
    refine ⟨78958739453856574639602055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105278319271808766186136073 78958739453856574639602055)
    ·
      refine ⟨118438109180784861959403083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78958739453856574639602055 118438109180784861959403083)
      ·
        refine ⟨177657163771177292939104625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118438109180784861959403083 177657163771177292939104625)
        ·
          refine ⟨133242872828382969704328469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177657163771177292939104625 133242872828382969704328469)
          ·
            refine ⟨6245759663830451704890397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133242872828382969704328469 6245759663830451704890397)
            ·
              refine ⟨2342159873936419389333899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6245759663830451704890397 2342159873936419389333899)
              ·
                refine ⟨3513239810904629084000849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342159873936419389333899 3513239810904629084000849)
                ·
                  refine ⟨2634929858178471813000637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3513239810904629084000849 2634929858178471813000637)
                  ·
                    refine ⟨988098696816926929875239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2634929858178471813000637 988098696816926929875239)
                    ·
                      rfl

theorem cell22_2886473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 2, 3].length) (baseStart_2886473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886473 prefixEnd_2886473 := by exact prefixLift 2886473
  have htrace : WordTrace (prefixWord ++ tailWord_2886473) baseStart_2886473 baseEnd_2886473 := by
    simpa [prefixWord, tailWord_2886473, baseEnd_2886473] using wordTrace_append hprefix tailTrace_2886473
  have hstable : (prefixWord ++ tailWord_2886473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886473).length < 2 ^ (prefixWord ++ tailWord_2886473).sum := by decide
  have hdescent : baseEnd_2886473 < baseStart_2886473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886514 : List Nat := [3, 2, 1, 2, 1, 1, 4, 1, 7]
def baseStart_2886514 : Nat := 118140960795 + 2886514 * 2 ^ 59
def prefixEnd_2886514 : Nat := 4983230072969 + 3 ^ 40 * 2886514 * 2
def baseEnd_2886514 : Nat := 329370910651605496533371

theorem tailTrace_2886514 : CollatzResearch.WordTrace tailWord_2886514 prefixEnd_2886514 329370910651605496533371 := by
  unfold tailWord_2886514
  simp only [CollatzResearch.WordTrace]
  refine ⟨26319953666165057547094649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70186543109773486792252397 26319953666165057547094649)
  ·
    refine ⟨19739965249623793160320987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26319953666165057547094649 19739965249623793160320987)
    ·
      refine ⟨29609947874435689740481481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19739965249623793160320987 29609947874435689740481481)
      ·
        refine ⟨22207460905826767305361111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29609947874435689740481481 22207460905826767305361111)
        ·
          refine ⟨33311191358740150958041667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22207460905826767305361111 33311191358740150958041667)
          ·
            refine ⟨49966787038110226437062501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33311191358740150958041667 49966787038110226437062501)
            ·
              refine ⟨9368772569645667456949219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49966787038110226437062501 9368772569645667456949219)
              ·
                refine ⟨14053158854468501185423829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9368772569645667456949219 14053158854468501185423829)
                ·
                  refine ⟨329370910651605496533371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14053158854468501185423829 329370910651605496533371)
                  ·
                    rfl

theorem cell22_2886514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 1, 7].length) (baseStart_2886514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886514 prefixEnd_2886514 := by exact prefixLift 2886514
  have htrace : WordTrace (prefixWord ++ tailWord_2886514) baseStart_2886514 baseEnd_2886514 := by
    simpa [prefixWord, tailWord_2886514, baseEnd_2886514] using wordTrace_append hprefix tailTrace_2886514
  have hstable : (prefixWord ++ tailWord_2886514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886514).length < 2 ^ (prefixWord ++ tailWord_2886514).sum := by decide
  have hdescent : baseEnd_2886514 < baseStart_2886514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886606 : List Nat := [4, 1, 1, 1, 2, 4, 1, 1, 1, 6]
def baseStart_2886606 : Nat := 118140960795 + 2886606 * 2 ^ 59
def prefixEnd_2886606 : Nat := 4983230072969 + 3 ^ 40 * 2886606 * 2
def baseEnd_2886606 : Nat := 988144225434958916299831

theorem tailTrace_2886606 : CollatzResearch.WordTrace tailWord_2886606 prefixEnd_2886606 988144225434958916299831 := by
  unfold tailWord_2886606
  simp only [CollatzResearch.WordTrace]
  refine ⟨13160396272540866237590959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70188780120217953267151781 13160396272540866237590959)
  ·
    refine ⟨19740594408811299356386439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13160396272540866237590959 19740594408811299356386439)
    ·
      refine ⟨29610891613216949034579659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19740594408811299356386439 29610891613216949034579659)
      ·
        refine ⟨44416337419825423551869489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29610891613216949034579659 44416337419825423551869489)
        ·
          refine ⟨33312253064869067663902117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44416337419825423551869489 33312253064869067663902117)
          ·
            refine ⟨6246047449662950186981647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33312253064869067663902117 6246047449662950186981647)
            ·
              refine ⟨9369071174494425280472471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246047449662950186981647 9369071174494425280472471)
              ·
                refine ⟨14053606761741637920708707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9369071174494425280472471 14053606761741637920708707)
                ·
                  refine ⟨21080410142612456881063061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14053606761741637920708707 21080410142612456881063061)
                  ·
                    refine ⟨988144225434958916299831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21080410142612456881063061 988144225434958916299831)
                    ·
                      rfl

theorem cell22_2886606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_2886606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886606 prefixEnd_2886606 := by exact prefixLift 2886606
  have htrace : WordTrace (prefixWord ++ tailWord_2886606) baseStart_2886606 baseEnd_2886606 := by
    simpa [prefixWord, tailWord_2886606, baseEnd_2886606] using wordTrace_append hprefix tailTrace_2886606
  have hstable : (prefixWord ++ tailWord_2886606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886606).length < 2 ^ (prefixWord ++ tailWord_2886606).sum := by decide
  have hdescent : baseEnd_2886606 < baseStart_2886606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886610 : List Nat := [3, 2, 2, 3, 1, 2, 2, 3, 4]
def baseStart_2886610 : Nat := 118140960795 + 2886610 * 2 ^ 59
def prefixEnd_2886610 : Nat := 4983230072969 + 3 ^ 40 * 2886610 * 2
def baseEnd_2886610 : Nat := 329381864905568079733273

theorem tailTrace_2886610 : CollatzResearch.WordTrace tailWord_2886610 prefixEnd_2886610 329381864905568079733273 := by
  unfold tailWord_2886610
  simp only [CollatzResearch.WordTrace]
  refine ⟨26320829018078109645968321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70188877381541625722582189 26320829018078109645968321)
  ·
    refine ⟨19740621763558582234476241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26320829018078109645968321 19740621763558582234476241)
    ·
      refine ⟨14805466322668936675857181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19740621763558582234476241 14805466322668936675857181)
      ·
        refine ⟨5552049871000851253446443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14805466322668936675857181 5552049871000851253446443)
        ·
          refine ⟨8328074806501276880169665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5552049871000851253446443 8328074806501276880169665)
          ·
            refine ⟨6246056104875957660127249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8328074806501276880169665 6246056104875957660127249)
            ·
              refine ⟨4684542078656968245095437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6246056104875957660127249 4684542078656968245095437)
              ·
                refine ⟨1756703279496363091910789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4684542078656968245095437 1756703279496363091910789)
                ·
                  refine ⟨329381864905568079733273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1756703279496363091910789 329381864905568079733273)
                  ·
                    rfl

theorem cell22_2886610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 3, 4].length) (baseStart_2886610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886610 prefixEnd_2886610 := by exact prefixLift 2886610
  have htrace : WordTrace (prefixWord ++ tailWord_2886610) baseStart_2886610 baseEnd_2886610 := by
    simpa [prefixWord, tailWord_2886610, baseEnd_2886610] using wordTrace_append hprefix tailTrace_2886610
  have hstable : (prefixWord ++ tailWord_2886610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886610).length < 2 ^ (prefixWord ++ tailWord_2886610).sum := by decide
  have hdescent : baseEnd_2886610 < baseStart_2886610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886621 : List Nat := [1, 4, 3, 1, 2, 2, 9]
def baseStart_2886621 : Nat := 118140960795 + 2886621 * 2 ^ 59
def prefixEnd_2886621 : Nat := 4983230072969 + 3 ^ 40 * 2886621 * 2
def baseEnd_2886621 : Nat := 36598124453389032487955

theorem tailTrace_2886621 : CollatzResearch.WordTrace tailWord_2886621 prefixEnd_2886621 36598124453389032487955 := by
  unfold tailWord_2886621
  simp only [CollatzResearch.WordTrace]
  refine ⟨105283717275272587462523717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70189144850181724975015811 105283717275272587462523717)
  ·
    refine ⟨19740696989113610149223197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105283717275272587462523717 19740696989113610149223197)
    ·
      refine ⟨7402761370917603805958699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19740696989113610149223197 7402761370917603805958699)
      ·
        refine ⟨11104142056376405708938049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7402761370917603805958699 11104142056376405708938049)
        ·
          refine ⟨8328106542282304281703537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11104142056376405708938049 8328106542282304281703537)
          ·
            refine ⟨6246079906711728211277653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8328106542282304281703537 6246079906711728211277653)
            ·
              refine ⟨36598124453389032487955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6246079906711728211277653 36598124453389032487955)
              ·
                rfl

theorem cell22_2886621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 9].length) (baseStart_2886621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886621 prefixEnd_2886621 := by exact prefixLift 2886621
  have htrace : WordTrace (prefixWord ++ tailWord_2886621) baseStart_2886621 baseEnd_2886621 := by
    simpa [prefixWord, tailWord_2886621, baseEnd_2886621] using wordTrace_append hprefix tailTrace_2886621
  have hstable : (prefixWord ++ tailWord_2886621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886621).length < 2 ^ (prefixWord ++ tailWord_2886621).sum := by decide
  have hdescent : baseEnd_2886621 < baseStart_2886621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886642 : List Nat := [3, 2, 1, 5, 2, 1, 1, 1, 1, 5]
def baseStart_2886642 : Nat := 118140960795 + 2886642 * 2 ^ 59
def prefixEnd_2886642 : Nat := 4983230072969 + 3 ^ 40 * 2886642 * 2
def baseEnd_2886642 : Nat := 988156548970666822399721

theorem tailTrace_2886642 : CollatzResearch.WordTrace tailWord_2886642 prefixEnd_2886642 988156548970666822399721 := by
  unfold tailWord_2886642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26321120802049127012259545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70189655472131005366025453 26321120802049127012259545)
  ·
    refine ⟨19740840601536845259194659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26321120802049127012259545 19740840601536845259194659)
    ·
      refine ⟨29611260902305267888791989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19740840601536845259194659 29611260902305267888791989)
      ·
        refine ⟨2776055709591118864574249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29611260902305267888791989 2776055709591118864574249)
        ·
          refine ⟨2082041782193339148430687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2776055709591118864574249 2082041782193339148430687)
          ·
            refine ⟨3123062673290008722646031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082041782193339148430687 3123062673290008722646031)
            ·
              refine ⟨4684594009935013083969047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123062673290008722646031 4684594009935013083969047)
              ·
                refine ⟨7026891014902519625953571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4684594009935013083969047 7026891014902519625953571)
                ·
                  refine ⟨10540336522353779438930357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7026891014902519625953571 10540336522353779438930357)
                  ·
                    refine ⟨988156548970666822399721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10540336522353779438930357 988156548970666822399721)
                    ·
                      rfl

theorem cell22_2886642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_2886642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886642 prefixEnd_2886642 := by exact prefixLift 2886642
  have htrace : WordTrace (prefixWord ++ tailWord_2886642) baseStart_2886642 baseEnd_2886642 := by
    simpa [prefixWord, tailWord_2886642, baseEnd_2886642] using wordTrace_append hprefix tailTrace_2886642
  have hstable : (prefixWord ++ tailWord_2886642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886642).length < 2 ^ (prefixWord ++ tailWord_2886642).sum := by decide
  have hdescent : baseEnd_2886642 < baseStart_2886642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886666 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 7]
def baseStart_2886666 : Nat := 118140960795 + 2886666 * 2 ^ 59
def prefixEnd_2886666 : Nat := 4983230072969 + 3 ^ 40 * 2886666 * 2
def baseEnd_2886666 : Nat := 329388254887046253266549

theorem tailTrace_2886666 : CollatzResearch.WordTrace tailWord_2886666 prefixEnd_2886666 329388254887046253266549 := by
  unfold tailWord_2886666
  simp only [CollatzResearch.WordTrace]
  refine ⟨26321339640027390036977963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70190239040073040098607901 26321339640027390036977963)
  ·
    refine ⟨39482009460041085055466945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26321339640027390036977963 39482009460041085055466945)
    ·
      refine ⟨29611507095030813791600209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39482009460041085055466945 29611507095030813791600209)
      ·
        refine ⟨22208630321273110343700157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29611507095030813791600209 22208630321273110343700157)
        ·
          refine ⟨8328236370477416378887559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22208630321273110343700157 8328236370477416378887559)
          ·
            refine ⟨12492354555716124568331339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8328236370477416378887559 12492354555716124568331339)
            ·
              refine ⟨18738531833574186852497009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12492354555716124568331339 18738531833574186852497009)
              ·
                refine ⟨14053898875180640139372757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18738531833574186852497009 14053898875180640139372757)
                ·
                  refine ⟨329388254887046253266549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14053898875180640139372757 329388254887046253266549)
                  ·
                    rfl

theorem cell22_2886666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 7].length) (baseStart_2886666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886666 prefixEnd_2886666 := by exact prefixLift 2886666
  have htrace : WordTrace (prefixWord ++ tailWord_2886666) baseStart_2886666 baseEnd_2886666 := by
    simpa [prefixWord, tailWord_2886666, baseEnd_2886666] using wordTrace_append hprefix tailTrace_2886666
  have hstable : (prefixWord ++ tailWord_2886666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886666).length < 2 ^ (prefixWord ++ tailWord_2886666).sum := by decide
  have hdescent : baseEnd_2886666 < baseStart_2886666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886687 : List Nat := [1, 1, 2, 4, 1, 4, 3, 2, 1, 3]
def baseStart_2886687 : Nat := 118140960795 + 2886687 * 2 ^ 59
def prefixEnd_2886687 : Nat := 4983230072969 + 3 ^ 40 * 2886687 * 2
def baseEnd_2886687 : Nat := 988171953390301705024583

theorem tailTrace_2886687 : CollatzResearch.WordTrace tailWord_2886687 prefixEnd_2886687 988171953390301705024583 := by
  unfold tailWord_2886687
  simp only [CollatzResearch.WordTrace]
  refine ⟨105286124493033480734426315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70190749662022320489617543 105286124493033480734426315)
  ·
    refine ⟨157929186739550221101639473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105286124493033480734426315 157929186739550221101639473)
    ·
      refine ⟨118446890054662665826229605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157929186739550221101639473 118446890054662665826229605)
      ·
        refine ⟨22208791885249249842418051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118446890054662665826229605 22208791885249249842418051)
        ·
          refine ⟨33313187827873874763627077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22208791885249249842418051 33313187827873874763627077)
          ·
            refine ⟨6246222717726351518180077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33313187827873874763627077 6246222717726351518180077)
            ·
              refine ⟨2342333519147381819317529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6246222717726351518180077 2342333519147381819317529)
              ·
                refine ⟨1756750139360536364488147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2342333519147381819317529 1756750139360536364488147)
                ·
                  refine ⟨2635125209040804546732221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756750139360536364488147 2635125209040804546732221)
                  ·
                    refine ⟨988171953390301705024583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2635125209040804546732221 988171953390301705024583)
                    ·
                      rfl

theorem cell22_2886687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 1, 3].length) (baseStart_2886687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886687 prefixEnd_2886687 := by exact prefixLift 2886687
  have htrace : WordTrace (prefixWord ++ tailWord_2886687) baseStart_2886687 baseEnd_2886687 := by
    simpa [prefixWord, tailWord_2886687, baseEnd_2886687] using wordTrace_append hprefix tailTrace_2886687
  have hstable : (prefixWord ++ tailWord_2886687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886687).length < 2 ^ (prefixWord ++ tailWord_2886687).sum := by decide
  have hdescent : baseEnd_2886687 < baseStart_2886687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886713 : List Nat := [1, 2, 1, 5, 2, 2, 1, 1, 3, 4]
def baseStart_2886713 : Nat := 118140960795 + 2886713 * 2 ^ 59
def prefixEnd_2886713 : Nat := 4983230072969 + 3 ^ 40 * 2886713 * 2
def baseEnd_2886713 : Nat := 988180853721646303874503

theorem tailTrace_2886713 : CollatzResearch.WordTrace tailWord_2886713 prefixEnd_2886713 988180853721646303874503 := by
  unfold tailWord_2886713
  simp only [CollatzResearch.WordTrace]
  refine ⟨105287072790939287174872793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70191381860626191449915195 105287072790939287174872793)
  ·
    refine ⟨78965304593204465381154595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105287072790939287174872793 78965304593204465381154595)
    ·
      refine ⟨118447956889806698071731893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78965304593204465381154595 118447956889806698071731893)
      ·
        refine ⟨11104495958419377944224865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118447956889806698071731893 11104495958419377944224865)
        ·
          refine ⟨8328371968814533458168649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11104495958419377944224865 8328371968814533458168649)
          ·
            refine ⟨6246278976610900093626487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8328371968814533458168649 6246278976610900093626487)
            ·
              refine ⟨9369418464916350140439731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246278976610900093626487 9369418464916350140439731)
              ·
                refine ⟨14054127697374525210659597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9369418464916350140439731 14054127697374525210659597)
                ·
                  refine ⟨5270297886515446953997349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14054127697374525210659597 5270297886515446953997349)
                  ·
                    refine ⟨988180853721646303874503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5270297886515446953997349 988180853721646303874503)
                    ·
                      rfl

theorem cell22_2886713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 4].length) (baseStart_2886713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886713 prefixEnd_2886713 := by exact prefixLift 2886713
  have htrace : WordTrace (prefixWord ++ tailWord_2886713) baseStart_2886713 baseEnd_2886713 := by
    simpa [prefixWord, tailWord_2886713, baseEnd_2886713] using wordTrace_append hprefix tailTrace_2886713
  have hstable : (prefixWord ++ tailWord_2886713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886713).length < 2 ^ (prefixWord ++ tailWord_2886713).sum := by decide
  have hdescent : baseEnd_2886713 < baseStart_2886713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886728 : List Nat := [2, 1, 3, 1, 1, 1, 4, 5, 4]
def baseStart_2886728 : Nat := 118140960795 + 2886728 * 2 ^ 59
def prefixEnd_2886728 : Nat := 4983230072969 + 3 ^ 40 * 2886728 * 2
def baseEnd_2886728 : Nat := 329395329509397088249819

theorem tailTrace_2886728 : CollatzResearch.WordTrace tailWord_2886728 prefixEnd_2886728 329395329509397088249819 := by
  unfold tailWord_2886728
  simp only [CollatzResearch.WordTrace]
  refine ⟨52643809942942472368334419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70191746590589963157779225 52643809942942472368334419)
  ·
    refine ⟨78965714914413708552501629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52643809942942472368334419 78965714914413708552501629)
    ·
      refine ⟨29612143092905140707188111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78965714914413708552501629 29612143092905140707188111)
      ·
        refine ⟨44418214639357711060782167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29612143092905140707188111 44418214639357711060782167)
        ·
          refine ⟨66627321959036566591173251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44418214639357711060782167 66627321959036566591173251)
          ·
            refine ⟨99940982938554849886759877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66627321959036566591173251 99940982938554849886759877)
            ·
              refine ⟨18738934300979034353767477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 99940982938554849886759877 18738934300979034353767477)
              ·
                refine ⟨1756775090716784470665701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18738934300979034353767477 1756775090716784470665701)
                ·
                  refine ⟨329395329509397088249819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1756775090716784470665701 329395329509397088249819)
                  ·
                    rfl

theorem cell22_2886728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 5, 4].length) (baseStart_2886728 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886728 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886728 prefixEnd_2886728 := by exact prefixLift 2886728
  have htrace : WordTrace (prefixWord ++ tailWord_2886728) baseStart_2886728 baseEnd_2886728 := by
    simpa [prefixWord, tailWord_2886728, baseEnd_2886728] using wordTrace_append hprefix tailTrace_2886728
  have hstable : (prefixWord ++ tailWord_2886728).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886728).length < 2 ^ (prefixWord ++ tailWord_2886728).sum := by decide
  have hdescent : baseEnd_2886728 < baseStart_2886728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886895 : List Nat := [1, 1, 2, 1, 7, 1, 1, 2, 1, 5]
def baseStart_2886895 : Nat := 118140960795 + 2886895 * 2 ^ 59
def prefixEnd_2886895 : Nat := 4983230072969 + 3 ^ 40 * 2886895 * 2
def baseEnd_2886895 : Nat := 988243156041058495823945

theorem tailTrace_2886895 : CollatzResearch.WordTrace tailWord_2886895 prefixEnd_2886895 988243156041058495823945 := by
  unfold tailWord_2886895
  simp only [CollatzResearch.WordTrace]
  refine ⟨105293710876279932257998139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70195807250853288171998759 105293710876279932257998139)
  ·
    refine ⟨157940566314419898386997209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105293710876279932257998139 157940566314419898386997209)
    ·
      refine ⟨118455424735814923790247907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 157940566314419898386997209 118455424735814923790247907)
      ·
        refine ⟨177683137103722385685371861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118455424735814923790247907 177683137103722385685371861)
        ·
          refine ⟨4164448525868493414500903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 177683137103722385685371861 4164448525868493414500903)
          ·
            refine ⟨6246672788802740121751355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164448525868493414500903 6246672788802740121751355)
            ·
              refine ⟨9370009183204110182627033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246672788802740121751355 9370009183204110182627033)
              ·
                refine ⟨7027506887403082636970275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9370009183204110182627033 7027506887403082636970275)
                ·
                  refine ⟨10541260331104623955455413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7027506887403082636970275 10541260331104623955455413)
                  ·
                    refine ⟨988243156041058495823945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10541260331104623955455413 988243156041058495823945)
                    ·
                      rfl

theorem cell22_2886895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 2, 1, 5].length) (baseStart_2886895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886895 prefixEnd_2886895 := by exact prefixLift 2886895
  have htrace : WordTrace (prefixWord ++ tailWord_2886895) baseStart_2886895 baseEnd_2886895 := by
    simpa [prefixWord, tailWord_2886895, baseEnd_2886895] using wordTrace_append hprefix tailTrace_2886895
  have hstable : (prefixWord ++ tailWord_2886895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886895).length < 2 ^ (prefixWord ++ tailWord_2886895).sum := by decide
  have hdescent : baseEnd_2886895 < baseStart_2886895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886908 : List Nat := [2, 2, 2, 1, 5, 10]
def baseStart_2886908 : Nat := 118140960795 + 2886908 * 2 ^ 59
def prefixEnd_2886908 : Nat := 4983230072969 + 3 ^ 40 * 2886908 * 2
def baseEnd_2886908 : Nat := 12200587730947293768505

theorem tailTrace_2886908 : CollatzResearch.WordTrace tailWord_2886908 prefixEnd_2886908 12200587730947293768505 := by
  unfold tailWord_2886908
  simp only [CollatzResearch.WordTrace]
  refine ⟨52647092512616417739110689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70196123350155223652147585 52647092512616417739110689)
  ·
    refine ⟨39485319384462313304333017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52647092512616417739110689 39485319384462313304333017)
    ·
      refine ⟨29613989538346734978249763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39485319384462313304333017 29613989538346734978249763)
      ·
        refine ⟨44420984307520102467374645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29613989538346734978249763 44420984307520102467374645)
        ·
          refine ⟨4164467278830009606316373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44420984307520102467374645 4164467278830009606316373)
          ·
            refine ⟨12200587730947293768505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4164467278830009606316373 12200587730947293768505)
            ·
              rfl

theorem cell22_2886908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 10].length) (baseStart_2886908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886908 prefixEnd_2886908 := by exact prefixLift 2886908
  have htrace : WordTrace (prefixWord ++ tailWord_2886908) baseStart_2886908 baseEnd_2886908 := by
    simpa [prefixWord, tailWord_2886908, baseEnd_2886908] using wordTrace_append hprefix tailTrace_2886908
  have hstable : (prefixWord ++ tailWord_2886908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886908).length < 2 ^ (prefixWord ++ tailWord_2886908).sum := by decide
  have hdescent : baseEnd_2886908 < baseStart_2886908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886914 : List Nat := [3, 4, 1, 1, 3, 1, 1, 4, 4]
def baseStart_2886914 : Nat := 118140960795 + 2886914 * 2 ^ 59
def prefixEnd_2886914 : Nat := 4983230072969 + 3 ^ 40 * 2886914 * 2
def baseEnd_2886914 : Nat := 329416553376449593199629

theorem tailTrace_2886914 : CollatzResearch.WordTrace tailWord_2886914 prefixEnd_2886914 329416553376449593199629 := by
  unfold tailWord_2886914
  simp only [CollatzResearch.WordTrace]
  refine ⟨26323600965802774625734949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70196269242140732335293197 26323600965802774625734949)
  ·
    refine ⟨4935675181088020242325303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26323600965802774625734949 4935675181088020242325303)
    ·
      refine ⟨7403512771632030363487955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4935675181088020242325303 7403512771632030363487955)
      ·
        refine ⟨11105269157448045545231933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7403512771632030363487955 11105269157448045545231933)
        ·
          refine ⟨4164475934043017079461975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11105269157448045545231933 4164475934043017079461975)
          ·
            refine ⟨6246713901064525619192963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164475934043017079461975 6246713901064525619192963)
            ·
              refine ⟨9370070851596788428789445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6246713901064525619192963 9370070851596788428789445)
              ·
                refine ⟨1756888284674397830398021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9370070851596788428789445 1756888284674397830398021)
                ·
                  refine ⟨329416553376449593199629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1756888284674397830398021 329416553376449593199629)
                  ·
                    rfl

theorem cell22_2886914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_2886914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886914 prefixEnd_2886914 := by exact prefixLift 2886914
  have htrace : WordTrace (prefixWord ++ tailWord_2886914) baseStart_2886914 baseEnd_2886914 := by
    simpa [prefixWord, tailWord_2886914, baseEnd_2886914] using wordTrace_append hprefix tailTrace_2886914
  have hstable : (prefixWord ++ tailWord_2886914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886914).length < 2 ^ (prefixWord ++ tailWord_2886914).sum := by decide
  have hdescent : baseEnd_2886914 < baseStart_2886914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886940 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 5, 3]
def baseStart_2886940 : Nat := 118140960795 + 2886940 * 2 ^ 59
def prefixEnd_2886940 : Nat := 4983230072969 + 3 ^ 40 * 2886940 * 2
def baseEnd_2886940 : Nat := 988258560460693378448807

theorem tailTrace_2886940 : CollatzResearch.WordTrace tailWord_2886940 prefixEnd_2886940 988258560460693378448807 := by
  unfold tailWord_2886940
  simp only [CollatzResearch.WordTrace]
  refine ⟨52647676080558452471693137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70196901440744603295590849 52647676080558452471693137)
  ·
    refine ⟨39485757060418839353769853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52647676080558452471693137 39485757060418839353769853)
    ·
      refine ⟨14807158897657064757663695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39485757060418839353769853 14807158897657064757663695)
      ·
        refine ⟨22210738346485597136495543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14807158897657064757663695 22210738346485597136495543)
        ·
          refine ⟨33316107519728395704743315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22210738346485597136495543 33316107519728395704743315)
          ·
            refine ⟨49974161279592593557114973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33316107519728395704743315 49974161279592593557114973)
            ·
              refine ⟨18740310479847222583918115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49974161279592593557114973 18740310479847222583918115)
              ·
                refine ⟨28110465719770833875877173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18740310479847222583918115 28110465719770833875877173)
                ·
                  refine ⟨2635356161228515675863485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28110465719770833875877173 2635356161228515675863485)
                  ·
                    refine ⟨988258560460693378448807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2635356161228515675863485 988258560460693378448807)
                    ·
                      rfl

theorem cell22_2886940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_2886940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886940 prefixEnd_2886940 := by exact prefixLift 2886940
  have htrace : WordTrace (prefixWord ++ tailWord_2886940) baseStart_2886940 baseEnd_2886940 := by
    simpa [prefixWord, tailWord_2886940, baseEnd_2886940] using wordTrace_append hprefix tailTrace_2886940
  have hstable : (prefixWord ++ tailWord_2886940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886940).length < 2 ^ (prefixWord ++ tailWord_2886940).sum := by decide
  have hdescent : baseEnd_2886940 < baseStart_2886940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886944 : List Nat := [2, 1, 1, 5, 4, 1, 1, 1, 2, 4]
def baseStart_2886944 : Nat := 118140960795 + 2886944 * 2 ^ 59
def prefixEnd_2886944 : Nat := 4983230072969 + 3 ^ 40 * 2886944 * 2
def baseEnd_2886944 : Nat := 988259929742438701348795

theorem tailTrace_2886944 : CollatzResearch.WordTrace tailWord_2886944 prefixEnd_2886944 988259929742438701348795 := by
  unfold tailWord_2886944
  simp only [CollatzResearch.WordTrace]
  refine ⟨52647749026551206813265943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70196998702068275751021257 52647749026551206813265943)
  ·
    refine ⟨78971623539826810219898915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52647749026551206813265943 78971623539826810219898915)
    ·
      refine ⟨118457435309740215329848373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78971623539826810219898915 118457435309740215329848373)
      ·
        refine ⟨11105384560288145187173285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118457435309740215329848373 11105384560288145187173285)
        ·
          refine ⟨2082259605054027222594991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11105384560288145187173285 2082259605054027222594991)
          ·
            refine ⟨3123389407581040833892487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082259605054027222594991 3123389407581040833892487)
            ·
              refine ⟨4685084111371561250838731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123389407581040833892487 4685084111371561250838731)
              ·
                refine ⟨7027626167057341876258097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685084111371561250838731 7027626167057341876258097)
                ·
                  refine ⟨5270719625293006407193573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7027626167057341876258097 5270719625293006407193573)
                  ·
                    refine ⟨988259929742438701348795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5270719625293006407193573 988259929742438701348795)
                    ·
                      rfl

theorem cell22_2886944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 2, 4].length) (baseStart_2886944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886944 prefixEnd_2886944 := by exact prefixLift 2886944
  have htrace : WordTrace (prefixWord ++ tailWord_2886944) baseStart_2886944 baseEnd_2886944 := by
    simpa [prefixWord, tailWord_2886944, baseEnd_2886944] using wordTrace_append hprefix tailTrace_2886944
  have hstable : (prefixWord ++ tailWord_2886944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886944).length < 2 ^ (prefixWord ++ tailWord_2886944).sum := by decide
  have hdescent : baseEnd_2886944 < baseStart_2886944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2886974 : List Nat := [4, 2, 1, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2886974 : Nat := 118140960795 + 2886974 * 2 ^ 59
def prefixEnd_2886974 : Nat := 4983230072969 + 3 ^ 40 * 2886974 * 2
def baseEnd_2886974 : Nat := 988270199355528623098703

theorem tailTrace_2886974 : CollatzResearch.WordTrace tailWord_2886974 prefixEnd_2886974 988270199355528623098703 := by
  unfold tailWord_2886974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13162074030374216093765497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70197728161995819166749317 13162074030374216093765497)
  ·
    refine ⟨9871555522780662070324123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13162074030374216093765497 9871555522780662070324123)
    ·
      refine ⟨14807333284170993105486185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9871555522780662070324123 14807333284170993105486185)
      ·
        refine ⟨11105499963128244829114639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14807333284170993105486185 11105499963128244829114639)
        ·
          refine ⟨16658249944692367243671959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11105499963128244829114639 16658249944692367243671959)
          ·
            refine ⟨24987374917038550865507939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16658249944692367243671959 24987374917038550865507939)
            ·
              refine ⟨37481062375557826298261909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24987374917038550865507939 37481062375557826298261909)
              ·
                refine ⟨1756924798854273107731027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37481062375557826298261909 1756924798854273107731027)
                ·
                  refine ⟨2635387198281409661596541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756924798854273107731027 2635387198281409661596541)
                  ·
                    refine ⟨988270199355528623098703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2635387198281409661596541 988270199355528623098703)
                    ·
                      rfl

theorem cell22_2886974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2886974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2886974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2886974 prefixEnd_2886974 := by exact prefixLift 2886974
  have htrace : WordTrace (prefixWord ++ tailWord_2886974) baseStart_2886974 baseEnd_2886974 := by
    simpa [prefixWord, tailWord_2886974, baseEnd_2886974] using wordTrace_append hprefix tailTrace_2886974
  have hstable : (prefixWord ++ tailWord_2886974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2886974).length < 2 ^ (prefixWord ++ tailWord_2886974).sum := by decide
  have hdescent : baseEnd_2886974 < baseStart_2886974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2886974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887038 : List Nat := [4, 2, 3, 2, 1, 2, 2, 1, 5]
def baseStart_2887038 : Nat := 118140960795 + 2887038 * 2 ^ 59
def prefixEnd_2887038 : Nat := 4983230072969 + 3 ^ 40 * 2887038 * 2
def baseEnd_2887038 : Nat := 329430702621151263166169

theorem tailTrace_2887038 : CollatzResearch.WordTrace tailWord_2887038 prefixEnd_2887038 329430702621151263166169 := by
  unfold tailWord_2887038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13162365814345233460056721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70199284343174578453635845 13162365814345233460056721)
  ·
    refine ⟨9871774360758925095042541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13162365814345233460056721 9871774360758925095042541)
    ·
      refine ⟨3701915385284596910640953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9871774360758925095042541 3701915385284596910640953)
      ·
        refine ⟨2776436538963447682980715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3701915385284596910640953 2776436538963447682980715)
        ·
          refine ⟨4164654808445171524471073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2776436538963447682980715 4164654808445171524471073)
          ·
            refine ⟨3123491106333878643353305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4164654808445171524471073 3123491106333878643353305)
            ·
              refine ⟨2342618329750408982514979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3123491106333878643353305 2342618329750408982514979)
              ·
                refine ⟨3513927494625613473772469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342618329750408982514979 3513927494625613473772469)
                ·
                  refine ⟨329430702621151263166169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3513927494625613473772469 329430702621151263166169)
                  ·
                    rfl

theorem cell22_2887038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 2, 2, 1, 5].length) (baseStart_2887038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887038 prefixEnd_2887038 := by exact prefixLift 2887038
  have htrace : WordTrace (prefixWord ++ tailWord_2887038) baseStart_2887038 baseEnd_2887038 := by
    simpa [prefixWord, tailWord_2887038, baseEnd_2887038] using wordTrace_append hprefix tailTrace_2887038
  have hstable : (prefixWord ++ tailWord_2887038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887038).length < 2 ^ (prefixWord ++ tailWord_2887038).sum := by decide
  have hdescent : baseEnd_2887038 < baseStart_2887038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887139 : List Nat := [1, 1, 1, 6, 2, 3, 1, 2, 5]
def baseStart_2887139 : Nat := 118140960795 + 2887139 * 2 ^ 59
def prefixEnd_2887139 : Nat := 4983230072969 + 3 ^ 40 * 2887139 * 2
def baseEnd_2887139 : Nat := 329442227409174397574399

theorem tailTrace_2887139 : CollatzResearch.WordTrace tailWord_2887139 prefixEnd_2887139 329442227409174397574399 := by
  unfold tailWord_2887139
  simp only [CollatzResearch.WordTrace]
  refine ⟨105302610287395961929880471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70201740191597307953253647 105302610287395961929880471)
  ·
    refine ⟨157953915431093942894820707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105302610287395961929880471 157953915431093942894820707)
    ·
      refine ⟨236930873146640914342231061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157953915431093942894820707 236930873146640914342231061)
      ·
        refine ⟨11106134678748792859792081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 236930873146640914342231061 11106134678748792859792081)
        ·
          refine ⟨8329601009061594644844061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11106134678748792859792081 8329601009061594644844061)
          ·
            refine ⟨3123600378398097991816523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8329601009061594644844061 3123600378398097991816523)
            ·
              refine ⟨4685400567597146987724785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3123600378398097991816523 4685400567597146987724785)
              ·
                refine ⟨3514050425697860240793589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4685400567597146987724785 3514050425697860240793589)
                ·
                  refine ⟨329442227409174397574399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3514050425697860240793589 329442227409174397574399)
                  ·
                    rfl

theorem cell22_2887139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 1, 2, 5].length) (baseStart_2887139 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887139 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887139 prefixEnd_2887139 := by exact prefixLift 2887139
  have htrace : WordTrace (prefixWord ++ tailWord_2887139) baseStart_2887139 baseEnd_2887139 := by
    simpa [prefixWord, tailWord_2887139, baseEnd_2887139] using wordTrace_append hprefix tailTrace_2887139
  have hstable : (prefixWord ++ tailWord_2887139).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887139).length < 2 ^ (prefixWord ++ tailWord_2887139).sum := by decide
  have hdescent : baseEnd_2887139 < baseStart_2887139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887201 : List Nat := [1, 2, 3, 2, 2, 3, 3, 2, 4]
def baseStart_2887201 : Nat := 118140960795 + 2887201 * 2 ^ 59
def prefixEnd_2887201 : Nat := 4983230072969 + 3 ^ 40 * 2887201 * 2
def baseEnd_2887201 : Nat := 329449302031525232557669

theorem tailTrace_2887201 : CollatzResearch.WordTrace tailWord_2887201 prefixEnd_2887201 329449302031525232557669 := by
  unfold tailWord_2887201
  simp only [CollatzResearch.WordTrace]
  refine ⟨105304871613171346518637457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70203247742114231012424971 105304871613171346518637457)
  ·
    refine ⟨78978653709878509888978093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105304871613171346518637457 78978653709878509888978093)
    ·
      refine ⟨29616995141204441208366785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78978653709878509888978093 29616995141204441208366785)
      ·
        refine ⟨22212746355903330906275089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29616995141204441208366785 22212746355903330906275089)
        ·
          refine ⟨16659559766927498179706317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22212746355903330906275089 16659559766927498179706317)
          ·
            refine ⟨6247334912597811817389869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16659559766927498179706317 6247334912597811817389869)
            ·
              refine ⟨2342750592224179431521201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6247334912597811817389869 2342750592224179431521201)
              ·
                refine ⟨1757062944168134573640901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2342750592224179431521201 1757062944168134573640901)
                ·
                  refine ⟨329449302031525232557669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1757062944168134573640901 329449302031525232557669)
                  ·
                    rfl

theorem cell22_2887201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 2, 4].length) (baseStart_2887201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887201 prefixEnd_2887201 := by exact prefixLift 2887201
  have htrace : WordTrace (prefixWord ++ tailWord_2887201) baseStart_2887201 baseEnd_2887201 := by
    simpa [prefixWord, tailWord_2887201, baseEnd_2887201] using wordTrace_append hprefix tailTrace_2887201
  have hstable : (prefixWord ++ tailWord_2887201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887201).length < 2 ^ (prefixWord ++ tailWord_2887201).sum := by decide
  have hdescent : baseEnd_2887201 < baseStart_2887201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887274 : List Nat := [3, 1, 3, 2, 1, 2, 2, 3, 5]
def baseStart_2887274 : Nat := 118140960795 + 2887274 * 2 ^ 59
def prefixEnd_2887274 : Nat := 4983230072969 + 3 ^ 40 * 2887274 * 2
def baseEnd_2887274 : Nat := 329457631828809280199261

theorem tailTrace_2887274 : CollatzResearch.WordTrace tailWord_2887274 prefixEnd_2887274 329457631828809280199261 := by
  unfold tailWord_2887274
  simp only [CollatzResearch.WordTrace]
  refine ⟨26326883535476719996511219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70205022761271253324029917 26326883535476719996511219)
  ·
    refine ⟨39490325303215079994766829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26326883535476719996511219 39490325303215079994766829)
    ·
      refine ⟨14808871988705654998037561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39490325303215079994766829 14808871988705654998037561)
      ·
        refine ⟨11106653991529241248528171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14808871988705654998037561 11106653991529241248528171)
        ·
          refine ⟨16659980987293861872792257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11106653991529241248528171 16659980987293861872792257)
          ·
            refine ⟨12494985740470396404594193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16659980987293861872792257 12494985740470396404594193)
            ·
              refine ⟨9371239305352797303445645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12494985740470396404594193 9371239305352797303445645)
              ·
                refine ⟨3514214739507298988792117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9371239305352797303445645 3514214739507298988792117)
                ·
                  refine ⟨329457631828809280199261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3514214739507298988792117 329457631828809280199261)
                  ·
                    rfl

theorem cell22_2887274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 3, 5].length) (baseStart_2887274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887274 prefixEnd_2887274 := by exact prefixLift 2887274
  have htrace : WordTrace (prefixWord ++ tailWord_2887274) baseStart_2887274 baseEnd_2887274 := by
    simpa [prefixWord, tailWord_2887274, baseEnd_2887274] using wordTrace_append hprefix tailTrace_2887274
  have hstable : (prefixWord ++ tailWord_2887274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887274).length < 2 ^ (prefixWord ++ tailWord_2887274).sum := by decide
  have hdescent : baseEnd_2887274 < baseStart_2887274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887317 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 3, 5]
def baseStart_2887317 : Nat := 118140960795 + 2887317 * 2 ^ 59
def prefixEnd_2887317 : Nat := 4983230072969 + 3 ^ 40 * 2887317 * 2
def baseEnd_2887317 : Nat := 988387615265190061772651

theorem tailTrace_2887317 : CollatzResearch.WordTrace tailWord_2887317 prefixEnd_2887317 988387615265190061772651 := by
  unfold tailWord_2887317
  simp only [CollatzResearch.WordTrace]
  refine ⟨105309102480751098329860205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70206068320500732219906803 105309102480751098329860205)
  ·
    refine ⟨39490913430281661873697577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105309102480751098329860205 39490913430281661873697577)
    ·
      refine ⟨29618185072711246405273183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39490913430281661873697577 29618185072711246405273183)
      ·
        refine ⟨44427277609066869607909775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29618185072711246405273183 44427277609066869607909775)
        ·
          refine ⟨66640916413600304411864663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44427277609066869607909775 66640916413600304411864663)
          ·
            refine ⟨99961374620400456617796995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66640916413600304411864663 99961374620400456617796995)
            ·
              refine ⟨149942061930600684926695493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99961374620400456617796995 149942061930600684926695493)
              ·
                refine ⟨28114136611987628423755405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 149942061930600684926695493 28114136611987628423755405)
                ·
                  refine ⟨10542801229495360658908277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28114136611987628423755405 10542801229495360658908277)
                  ·
                    refine ⟨988387615265190061772651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10542801229495360658908277 988387615265190061772651)
                    ·
                      rfl

theorem cell22_2887317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_2887317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887317 prefixEnd_2887317 := by exact prefixLift 2887317
  have htrace : WordTrace (prefixWord ++ tailWord_2887317) baseStart_2887317 baseEnd_2887317 := by
    simpa [prefixWord, tailWord_2887317, baseEnd_2887317] using wordTrace_append hprefix tailTrace_2887317
  have hstable : (prefixWord ++ tailWord_2887317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887317).length < 2 ^ (prefixWord ++ tailWord_2887317).sum := by decide
  have hdescent : baseEnd_2887317 < baseStart_2887317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887319 : List Nat := [1, 1, 3, 3, 2, 3, 2, 1, 6]
def baseStart_2887319 : Nat := 118140960795 + 2887319 * 2 ^ 59
def prefixEnd_2887319 : Nat := 4983230072969 + 3 ^ 40 * 2887319 * 2
def baseEnd_2887319 : Nat := 329462766635354241074215

theorem tailTrace_2887319 : CollatzResearch.WordTrace tailWord_2887319 prefixEnd_2887319 329462766635354241074215 := by
  unfold tailWord_2887319
  simp only [CollatzResearch.WordTrace]
  refine ⟨105309175426743852671433011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70206116951162568447622007 105309175426743852671433011)
  ·
    refine ⟨157963763140115779007149517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105309175426743852671433011 157963763140115779007149517)
    ·
      refine ⟨59236411177543417127681069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 157963763140115779007149517 59236411177543417127681069)
      ·
        refine ⟨22213654191578781422880401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59236411177543417127681069 22213654191578781422880401)
        ·
          refine ⟨16660240643684086067160301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22213654191578781422880401 16660240643684086067160301)
          ·
            refine ⟨6247590241381532275185113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16660240643684086067160301 6247590241381532275185113)
            ·
              refine ⟨4685692681036149206388835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6247590241381532275185113 4685692681036149206388835)
              ·
                refine ⟨7028539021554223809583253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4685692681036149206388835 7028539021554223809583253)
                ·
                  refine ⟨329462766635354241074215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7028539021554223809583253 329462766635354241074215)
                  ·
                    rfl

theorem cell22_2887319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 2, 1, 6].length) (baseStart_2887319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887319 prefixEnd_2887319 := by exact prefixLift 2887319
  have htrace : WordTrace (prefixWord ++ tailWord_2887319) baseStart_2887319 baseEnd_2887319 := by
    simpa [prefixWord, tailWord_2887319, baseEnd_2887319] using wordTrace_append hprefix tailTrace_2887319
  have hstable : (prefixWord ++ tailWord_2887319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887319).length < 2 ^ (prefixWord ++ tailWord_2887319).sum := by decide
  have hdescent : baseEnd_2887319 < baseStart_2887319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887347 : List Nat := [1, 1, 1, 2, 3, 3, 3, 8]
def baseStart_2887347 : Nat := 118140960795 + 2887347 * 2 ^ 59
def prefixEnd_2887347 : Nat := 4983230072969 + 3 ^ 40 * 2887347 * 2
def baseEnd_2887347 : Nat := 109821987208697775946951

theorem tailTrace_2887347 : CollatzResearch.WordTrace tailWord_2887347 prefixEnd_2887347 109821987208697775946951 := by
  unfold tailWord_2887347
  simp only [CollatzResearch.WordTrace]
  refine ⟨105310196670642413453452295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70206797780428275635634863 105310196670642413453452295)
  ·
    refine ⟨157965295005963620180178443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105310196670642413453452295 157965295005963620180178443)
    ·
      refine ⟨236947942508945430270267665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157965295005963620180178443 236947942508945430270267665)
      ·
        refine ⟨177710956881709072702700749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 236947942508945430270267665 177710956881709072702700749)
        ·
          refine ⟨66641608830640902263512781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 177710956881709072702700749 66641608830640902263512781)
          ·
            refine ⟨24990603311490338348817293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66641608830640902263512781 24990603311490338348817293)
            ·
              refine ⟨9371476241808876880806485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24990603311490338348817293 9371476241808876880806485)
              ·
                refine ⟨109821987208697775946951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9371476241808876880806485 109821987208697775946951)
                ·
                  rfl

theorem cell22_2887347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 8].length) (baseStart_2887347 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887347 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887347 prefixEnd_2887347 := by exact prefixLift 2887347
  have htrace : WordTrace (prefixWord ++ tailWord_2887347) baseStart_2887347 baseEnd_2887347 := by
    simpa [prefixWord, tailWord_2887347, baseEnd_2887347] using wordTrace_append hprefix tailTrace_2887347
  have hstable : (prefixWord ++ tailWord_2887347).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887347).length < 2 ^ (prefixWord ++ tailWord_2887347).sum := by decide
  have hdescent : baseEnd_2887347 < baseStart_2887347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887456 : List Nat := [2, 1, 1, 5, 1, 1, 2, 4, 1, 4]
def baseStart_2887456 : Nat := 118140960795 + 2887456 * 2 ^ 59
def prefixEnd_2887456 : Nat := 4983230072969 + 3 ^ 40 * 2887456 * 2
def baseEnd_2887456 : Nat := 988435197805840032547225

theorem tailTrace_2887456 : CollatzResearch.WordTrace tailWord_2887456 prefixEnd_2887456 988435197805840032547225 := by
  unfold tailWord_2887456
  simp only [CollatzResearch.WordTrace]
  refine ⟨52657086113623762534585111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70209448151498350046113481 52657086113623762534585111)
  ·
    refine ⟨78985629170435643801877667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52657086113623762534585111 78985629170435643801877667)
    ·
      refine ⟨118478443755653465702816501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78985629170435643801877667 118478443755653465702816501)
      ·
        refine ⟨11107354102092512409639047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 118478443755653465702816501 11107354102092512409639047)
        ·
          refine ⟨16661031153138768614458571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11107354102092512409639047 16661031153138768614458571)
          ·
            refine ⟨24991546729708152921687857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16661031153138768614458571 24991546729708152921687857)
            ·
              refine ⟨18743660047281114691265893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24991546729708152921687857 18743660047281114691265893)
              ·
                refine ⟨3514436258865209004612355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18743660047281114691265893 3514436258865209004612355)
                ·
                  refine ⟨5271654388297813506918533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514436258865209004612355 5271654388297813506918533)
                  ·
                    refine ⟨988435197805840032547225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5271654388297813506918533 988435197805840032547225)
                    ·
                      rfl

theorem cell22_2887456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 1, 4].length) (baseStart_2887456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887456 prefixEnd_2887456 := by exact prefixLift 2887456
  have htrace : WordTrace (prefixWord ++ tailWord_2887456) baseStart_2887456 baseEnd_2887456 := by
    simpa [prefixWord, tailWord_2887456, baseEnd_2887456] using wordTrace_append hprefix tailTrace_2887456
  have hstable : (prefixWord ++ tailWord_2887456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887456).length < 2 ^ (prefixWord ++ tailWord_2887456).sum := by decide
  have hdescent : baseEnd_2887456 < baseStart_2887456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887473 : List Nat := [1, 2, 2, 3, 2, 2, 4, 1, 1, 4]
def baseStart_2887473 : Nat := 118140960795 + 2887473 * 2 ^ 59
def prefixEnd_2887473 : Nat := 4983230072969 + 3 ^ 40 * 2887473 * 2
def baseEnd_2887473 : Nat := 988441017253257654872173

theorem tailTrace_2887473 : CollatzResearch.WordTrace tailWord_2887473 prefixEnd_2887473 988441017253257654872173 := by
  unfold tailWord_2887473
  simp only [CollatzResearch.WordTrace]
  refine ⟨105314792268185936972539073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70209861512123957981692715 105314792268185936972539073)
  ·
    refine ⟨78986094201139452729404305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105314792268185936972539073 78986094201139452729404305)
    ·
      refine ⟨59239570650854589547053229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 78986094201139452729404305 59239570650854589547053229)
      ·
        refine ⟨22214838994070471080144961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59239570650854589547053229 22214838994070471080144961)
        ·
          refine ⟨16661129245552853310108721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22214838994070471080144961 16661129245552853310108721)
          ·
            refine ⟨12495846934164639982581541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16661129245552853310108721 12495846934164639982581541)
            ·
              refine ⟨2342971300155869996734039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12495846934164639982581541 2342971300155869996734039)
              ·
                refine ⟨3514456950233804995101059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2342971300155869996734039 3514456950233804995101059)
                ·
                  refine ⟨5271685425350707492651589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514456950233804995101059 5271685425350707492651589)
                  ·
                    refine ⟨988441017253257654872173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5271685425350707492651589 988441017253257654872173)
                    ·
                      rfl

theorem cell22_2887473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 4, 1, 1, 4].length) (baseStart_2887473 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887473 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887473 prefixEnd_2887473 := by exact prefixLift 2887473
  have htrace : WordTrace (prefixWord ++ tailWord_2887473) baseStart_2887473 baseEnd_2887473 := by
    simpa [prefixWord, tailWord_2887473, baseEnd_2887473] using wordTrace_append hprefix tailTrace_2887473
  have hstable : (prefixWord ++ tailWord_2887473).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887473).length < 2 ^ (prefixWord ++ tailWord_2887473).sum := by decide
  have hdescent : baseEnd_2887473 < baseStart_2887473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887514 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 2, 7]
def baseStart_2887514 : Nat := 118140960795 + 2887514 * 2 ^ 59
def prefixEnd_2887514 : Nat := 4983230072969 + 3 ^ 40 * 2887514 * 2
def baseEnd_2887514 : Nat := 988455052391147214597047

theorem tailTrace_2887514 : CollatzResearch.WordTrace tailWord_2887514 prefixEnd_2887514 988455052391147214597047 := by
  unfold tailWord_2887514
  simp only [CollatzResearch.WordTrace]
  refine ⟨26329071915259350243695399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70210858440691600649854397 26329071915259350243695399)
  ·
    refine ⟨39493607872889025365543099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26329071915259350243695399 39493607872889025365543099)
    ·
      refine ⟨59240411809333538048314649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39493607872889025365543099 59240411809333538048314649)
      ·
        refine ⟨44430308857000153536235987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59240411809333538048314649 44430308857000153536235987)
        ·
          refine ⟨66645463285500230304353981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44430308857000153536235987 66645463285500230304353981)
          ·
            refine ⟨24992048732062586364132743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66645463285500230304353981 24992048732062586364132743)
            ·
              refine ⟨37488073098093879546199115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24992048732062586364132743 37488073098093879546199115)
              ·
                refine ⟨56232109647140819319298673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37488073098093879546199115 56232109647140819319298673)
                ·
                  refine ⟨42174082235355614489474005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56232109647140819319298673 42174082235355614489474005)
                  ·
                    refine ⟨988455052391147214597047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42174082235355614489474005 988455052391147214597047)
                    ·
                      rfl

theorem cell22_2887514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 7].length) (baseStart_2887514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887514 prefixEnd_2887514 := by exact prefixLift 2887514
  have htrace : WordTrace (prefixWord ++ tailWord_2887514) baseStart_2887514 baseEnd_2887514 := by
    simpa [prefixWord, tailWord_2887514, baseEnd_2887514] using wordTrace_append hprefix tailTrace_2887514
  have hstable : (prefixWord ++ tailWord_2887514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887514).length < 2 ^ (prefixWord ++ tailWord_2887514).sum := by decide
  have hdescent : baseEnd_2887514 < baseStart_2887514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887561 : List Nat := [1, 2, 1, 1, 5, 1, 3, 3, 5]
def baseStart_2887561 : Nat := 118140960795 + 2887561 * 2 ^ 59
def prefixEnd_2887561 : Nat := 4983230072969 + 3 ^ 40 * 2887561 * 2
def baseEnd_2887561 : Nat := 329490380483884919557301

theorem tailTrace_2887561 : CollatzResearch.WordTrace tailWord_2887561 prefixEnd_2887561 329490380483884919557301 := by
  unfold tailWord_2887561
  simp only [CollatzResearch.WordTrace]
  refine ⟨105318001891867128001742537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70212001261244752001161691 105318001891867128001742537)
  ·
    refine ⟨78988501418900346001306903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105318001891867128001742537 78988501418900346001306903)
    ·
      refine ⟨118482752128350519001960355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 78988501418900346001306903 118482752128350519001960355)
      ·
        refine ⟨177724128192525778502940533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118482752128350519001960355 177724128192525778502940533)
        ·
          refine ⟨16661637018049291734650675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177724128192525778502940533 16661637018049291734650675)
          ·
            refine ⟨24992455527073937601976013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16661637018049291734650675 24992455527073937601976013)
            ·
              refine ⟨9372170822652726600741005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24992455527073937601976013 9372170822652726600741005)
              ·
                refine ⟨3514564058494772475277877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9372170822652726600741005 3514564058494772475277877)
                ·
                  refine ⟨329490380483884919557301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3514564058494772475277877 329490380483884919557301)
                  ·
                    rfl

theorem cell22_2887561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 3, 5].length) (baseStart_2887561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887561 prefixEnd_2887561 := by exact prefixLift 2887561
  have htrace : WordTrace (prefixWord ++ tailWord_2887561) baseStart_2887561 baseEnd_2887561 := by
    simpa [prefixWord, tailWord_2887561, baseEnd_2887561] using wordTrace_append hprefix tailTrace_2887561
  have hstable : (prefixWord ++ tailWord_2887561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887561).length < 2 ^ (prefixWord ++ tailWord_2887561).sum := by decide
  have hdescent : baseEnd_2887561 < baseStart_2887561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887642 : List Nat := [3, 1, 1, 2, 5, 2, 2, 1, 1, 4]
def baseStart_2887642 : Nat := 118140960795 + 2887642 * 2 ^ 59
def prefixEnd_2887642 : Nat := 4983230072969 + 3 ^ 40 * 2887642 * 2
def baseEnd_2887642 : Nat := 988498869406997547396655

theorem tailTrace_2887642 : CollatzResearch.WordTrace tailWord_2887642 prefixEnd_2887642 988498869406997547396655 := by
  unfold tailWord_2887642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26330239051143419708860295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70213970803049119223627453 26330239051143419708860295)
  ·
    refine ⟨39495358576715129563290443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26330239051143419708860295 39495358576715129563290443)
    ·
      refine ⟨59243037865072694344935665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39495358576715129563290443 59243037865072694344935665)
      ·
        refine ⟨44432278398804520758701749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59243037865072694344935665 44432278398804520758701749)
        ·
          refine ⟨4165526099887923821128289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44432278398804520758701749 4165526099887923821128289)
          ·
            refine ⟨3124144574915942865846217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4165526099887923821128289 3124144574915942865846217)
            ·
              refine ⟨2343108431186957149384663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3124144574915942865846217 2343108431186957149384663)
              ·
                refine ⟨3514662646780435724076995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343108431186957149384663 3514662646780435724076995)
                ·
                  refine ⟨5271993970170653586115493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514662646780435724076995 5271993970170653586115493)
                  ·
                    refine ⟨988498869406997547396655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5271993970170653586115493 988498869406997547396655)
                    ·
                      rfl

theorem cell22_2887642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 1, 4].length) (baseStart_2887642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887642 prefixEnd_2887642 := by exact prefixLift 2887642
  have htrace : WordTrace (prefixWord ++ tailWord_2887642) baseStart_2887642 baseEnd_2887642 := by
    simpa [prefixWord, tailWord_2887642, baseEnd_2887642] using wordTrace_append hprefix tailTrace_2887642
  have hstable : (prefixWord ++ tailWord_2887642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887642).length < 2 ^ (prefixWord ++ tailWord_2887642).sum := by decide
  have hdescent : baseEnd_2887642 < baseStart_2887642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887651 : List Nat := [1, 1, 1, 6, 1, 3, 9]
def baseStart_2887651 : Nat := 118140960795 + 2887651 * 2 ^ 59
def prefixEnd_2887651 : Nat := 4983230072969 + 3 ^ 40 * 2887651 * 2
def baseEnd_2887651 : Nat := 36611183344108315700801

theorem tailTrace_2887651 : CollatzResearch.WordTrace tailWord_2887651 prefixEnd_2887651 36611183344108315700801 := by
  unfold tailWord_2887651
  simp only [CollatzResearch.WordTrace]
  refine ⟨105321284461541073372518807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70214189641027382248345871 105321284461541073372518807)
  ·
    refine ⟨157981926692311610058778211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105321284461541073372518807 157981926692311610058778211)
    ·
      refine ⟨236972890038467415088167317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 157981926692311610058778211 236972890038467415088167317)
      ·
        refine ⟨11108104220553160082257843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 236972890038467415088167317 11108104220553160082257843)
        ·
          refine ⟨16662156330829740123386765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11108104220553160082257843 16662156330829740123386765)
          ·
            refine ⟨6248308624061152546270037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16662156330829740123386765 6248308624061152546270037)
            ·
              refine ⟨36611183344108315700801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6248308624061152546270037 36611183344108315700801)
              ·
                rfl

theorem cell22_2887651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 9].length) (baseStart_2887651 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887651 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887651 prefixEnd_2887651 := by exact prefixLift 2887651
  have htrace : WordTrace (prefixWord ++ tailWord_2887651) baseStart_2887651 baseEnd_2887651 := by
    simpa [prefixWord, tailWord_2887651, baseEnd_2887651] using wordTrace_append hprefix tailTrace_2887651
  have hstable : (prefixWord ++ tailWord_2887651).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887651).length < 2 ^ (prefixWord ++ tailWord_2887651).sum := by decide
  have hdescent : baseEnd_2887651 < baseStart_2887651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887655 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 4, 3]
def baseStart_2887655 : Nat := 118140960795 + 2887655 * 2 ^ 59
def prefixEnd_2887655 : Nat := 4983230072969 + 3 ^ 40 * 2887655 * 2
def baseEnd_2887655 : Nat := 988503319572669846821615

theorem tailTrace_2887655 : CollatzResearch.WordTrace tailWord_2887655 prefixEnd_2887655 988503319572669846821615 := by
  unfold tailWord_2887655
  simp only [CollatzResearch.WordTrace]
  refine ⟨105321430353526582055664419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70214286902351054703776279 105321430353526582055664419)
  ·
    refine ⟨157982145530289873083496629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105321430353526582055664419 157982145530289873083496629)
    ·
      refine ⟨14810826143464675601577809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 157982145530289873083496629 14810826143464675601577809)
      ·
        refine ⟨11108119607598506701183357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14810826143464675601577809 11108119607598506701183357)
        ·
          refine ⟨4165544852849440012943759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11108119607598506701183357 4165544852849440012943759)
          ·
            refine ⟨6248317279274160019415639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4165544852849440012943759 6248317279274160019415639)
            ·
              refine ⟨9372475918911240029123459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6248317279274160019415639 9372475918911240029123459)
              ·
                refine ⟨14058713878366860043685189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9372475918911240029123459 14058713878366860043685189)
                ·
                  refine ⟨2636008852193786258190973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14058713878366860043685189 2636008852193786258190973)
                  ·
                    refine ⟨988503319572669846821615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2636008852193786258190973 988503319572669846821615)
                    ·
                      rfl

theorem cell22_2887655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_2887655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887655 prefixEnd_2887655 := by exact prefixLift 2887655
  have htrace : WordTrace (prefixWord ++ tailWord_2887655) baseStart_2887655 baseEnd_2887655 := by
    simpa [prefixWord, tailWord_2887655, baseEnd_2887655] using wordTrace_append hprefix tailTrace_2887655
  have hstable : (prefixWord ++ tailWord_2887655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887655).length < 2 ^ (prefixWord ++ tailWord_2887655).sum := by decide
  have hdescent : baseEnd_2887655 < baseStart_2887655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887730 : List Nat := [3, 2, 1, 1, 2, 3, 4, 1, 5]
def baseStart_2887730 : Nat := 118140960795 + 2887730 * 2 ^ 59
def prefixEnd_2887730 : Nat := 4983230072969 + 3 ^ 40 * 2887730 * 2
def baseEnd_2887730 : Nat := 329509664535131550398795

theorem tailTrace_2887730 : CollatzResearch.WordTrace tailWord_2887730 prefixEnd_2887730 329509664535131550398795 := by
  unfold tailWord_2887730
  simp only [CollatzResearch.WordTrace]
  refine ⟨26331041457063717466161161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70216110552169913243096429 26331041457063717466161161)
  ·
    refine ⟨19748281092797788099620871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26331041457063717466161161 19748281092797788099620871)
    ·
      refine ⟨29622421639196682149431307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19748281092797788099620871 29622421639196682149431307)
      ·
        refine ⟨44433632458795023224146961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29622421639196682149431307 44433632458795023224146961)
        ·
          refine ⟨33325224344096267418110221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44433632458795023224146961 33325224344096267418110221)
          ·
            refine ⟨12496959129036100281791333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33325224344096267418110221 12496959129036100281791333)
            ·
              refine ⟨2343179836694268802835875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12496959129036100281791333 2343179836694268802835875)
              ·
                refine ⟨3514769755041403204253813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343179836694268802835875 3514769755041403204253813)
                ·
                  refine ⟨329509664535131550398795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3514769755041403204253813 329509664535131550398795)
                  ·
                    rfl

theorem cell22_2887730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_2887730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887730 prefixEnd_2887730 := by exact prefixLift 2887730
  have htrace : WordTrace (prefixWord ++ tailWord_2887730) baseStart_2887730 baseEnd_2887730 := by
    simpa [prefixWord, tailWord_2887730, baseEnd_2887730] using wordTrace_append hprefix tailTrace_2887730
  have hstable : (prefixWord ++ tailWord_2887730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887730).length < 2 ^ (prefixWord ++ tailWord_2887730).sum := by decide
  have hdescent : baseEnd_2887730 < baseStart_2887730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887790 : List Nat := [4, 1, 2, 2, 1, 1, 4, 1, 1, 5]
def baseStart_2887790 : Nat := 118140960795 + 2887790 * 2 ^ 59
def prefixEnd_2887790 : Nat := 4983230072969 + 3 ^ 40 * 2887790 * 2
def baseEnd_2887790 : Nat := 988549532831574494696201

theorem tailTrace_2887790 : CollatzResearch.WordTrace tailWord_2887790 prefixEnd_2887790 988549532831574494696201 := by
  unfold tailWord_2887790
  simp only [CollatzResearch.WordTrace]
  refine ⟨13165794276004687513978603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70217569472025000074552549 13165794276004687513978603)
  ·
    refine ⟨19748691414007031270967905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13165794276004687513978603 19748691414007031270967905)
    ·
      refine ⟨14811518560505273453225929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19748691414007031270967905 14811518560505273453225929)
      ·
        refine ⟨11108638920378955089919447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14811518560505273453225929 11108638920378955089919447)
        ·
          refine ⟨16662958380568432634879171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11108638920378955089919447 16662958380568432634879171)
          ·
            refine ⟨24994437570852648952318757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16662958380568432634879171 24994437570852648952318757)
            ·
              refine ⟨4686457044534871678559767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24994437570852648952318757 4686457044534871678559767)
              ·
                refine ⟨7029685566802307517839651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4686457044534871678559767 7029685566802307517839651)
                ·
                  refine ⟨10544528350203461276759477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7029685566802307517839651 10544528350203461276759477)
                  ·
                    refine ⟨988549532831574494696201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10544528350203461276759477 988549532831574494696201)
                    ·
                      rfl

theorem cell22_2887790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 4, 1, 1, 5].length) (baseStart_2887790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887790 prefixEnd_2887790 := by exact prefixLift 2887790
  have htrace : WordTrace (prefixWord ++ tailWord_2887790) baseStart_2887790 baseEnd_2887790 := by
    simpa [prefixWord, tailWord_2887790, baseEnd_2887790] using wordTrace_append hprefix tailTrace_2887790
  have hstable : (prefixWord ++ tailWord_2887790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887790).length < 2 ^ (prefixWord ++ tailWord_2887790).sum := by decide
  have hdescent : baseEnd_2887790 < baseStart_2887790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887805 : List Nat := [1, 4, 1, 1, 3, 2, 3, 1, 2, 4]
def baseStart_2887805 : Nat := 118140960795 + 2887805 * 2 ^ 59
def prefixEnd_2887805 : Nat := 4983230072969 + 3 ^ 40 * 2887805 * 2
def baseEnd_2887805 : Nat := 988554667638119455571155

theorem tailTrace_2887805 : CollatzResearch.WordTrace tailWord_2887805 prefixEnd_2887805 988554667638119455571155 := by
  unfold tailWord_2887805
  simp only [CollatzResearch.WordTrace]
  refine ⟨105326901302983157673624869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70217934201988771782416579 105326901302983157673624869)
  ·
    refine ⟨19748793994309342063804663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105326901302983157673624869 19748793994309342063804663)
    ·
      refine ⟨29623190991464013095706995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19748793994309342063804663 29623190991464013095706995)
      ·
        refine ⟨44434786487196019643560493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29623190991464013095706995 44434786487196019643560493)
        ·
          refine ⟨16663044932698507366335185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44434786487196019643560493 16663044932698507366335185)
          ·
            refine ⟨12497283699523880524751389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16663044932698507366335185 12497283699523880524751389)
            ·
              refine ⟨4686481387321455196781771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12497283699523880524751389 4686481387321455196781771)
              ·
                refine ⟨7029722080982182795172657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4686481387321455196781771 7029722080982182795172657)
                ·
                  refine ⟨5272291560736637096379493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7029722080982182795172657 5272291560736637096379493)
                  ·
                    refine ⟨988554667638119455571155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5272291560736637096379493 988554667638119455571155)
                    ·
                      rfl

theorem cell22_2887805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_2887805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887805 prefixEnd_2887805 := by exact prefixLift 2887805
  have htrace : WordTrace (prefixWord ++ tailWord_2887805) baseStart_2887805 baseEnd_2887805 := by
    simpa [prefixWord, tailWord_2887805, baseEnd_2887805] using wordTrace_append hprefix tailTrace_2887805
  have hstable : (prefixWord ++ tailWord_2887805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887805).length < 2 ^ (prefixWord ++ tailWord_2887805).sum := by decide
  have hdescent : baseEnd_2887805 < baseStart_2887805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887860 : List Nat := [2, 5, 3, 1, 2, 1, 1, 3, 4]
def baseStart_2887860 : Nat := 118140960795 + 2887860 * 2 ^ 59
def prefixEnd_2887860 : Nat := 4983230072969 + 3 ^ 40 * 2887860 * 2
def baseEnd_2887860 : Nat := 329524498420705881815329

theorem tailTrace_2887860 : CollatzResearch.WordTrace tailWord_2887860 prefixEnd_2887860 329524498420705881815329 := by
  unfold tailWord_2887860
  simp only [CollatzResearch.WordTrace]
  refine ⟨52664453658891951033438517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70219271545189268044584689 52664453658891951033438517)
  ·
    refine ⟨4937292530521120409384861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52664453658891951033438517 4937292530521120409384861)
    ·
      refine ⟨1851484698945420153519323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4937292530521120409384861 1851484698945420153519323)
      ·
        refine ⟨2777227048418130230278985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1851484698945420153519323 2777227048418130230278985)
        ·
          refine ⟨2082920286313597672709239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2777227048418130230278985 2082920286313597672709239)
          ·
            refine ⟨3124380429470396509063859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2082920286313597672709239 3124380429470396509063859)
            ·
              refine ⟨4686570644205594763595789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3124380429470396509063859 4686570644205594763595789)
              ·
                refine ⟨1757463991577098036348421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4686570644205594763595789 1757463991577098036348421)
                ·
                  refine ⟨329524498420705881815329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1757463991577098036348421 329524498420705881815329)
                  ·
                    rfl

theorem cell22_2887860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_2887860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887860 prefixEnd_2887860 := by exact prefixLift 2887860
  have htrace : WordTrace (prefixWord ++ tailWord_2887860) baseStart_2887860 baseEnd_2887860 := by
    simpa [prefixWord, tailWord_2887860, baseEnd_2887860] using wordTrace_append hprefix tailTrace_2887860
  have hstable : (prefixWord ++ tailWord_2887860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887860).length < 2 ^ (prefixWord ++ tailWord_2887860).sum := by decide
  have hdescent : baseEnd_2887860 < baseStart_2887860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887886 : List Nat := [4, 1, 1, 1, 4, 2, 3, 2, 1, 3]
def baseStart_2887886 : Nat := 118140960795 + 2887886 * 2 ^ 59
def prefixEnd_2887886 : Nat := 4983230072969 + 3 ^ 40 * 2887886 * 2
def baseEnd_2887886 : Nat := 988582395593462244295907

theorem tailTrace_2887886 : CollatzResearch.WordTrace tailWord_2887886 prefixEnd_2887886 988582395593462244295907 := by
  unfold tailWord_2887886
  simp only [CollatzResearch.WordTrace]
  refine ⟨13166231951961213563415439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70219903743793139004882341 13166231951961213563415439)
  ·
    refine ⟨19749347927941820345123159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13166231951961213563415439 19749347927941820345123159)
    ·
      refine ⟨29624021891912730517684739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19749347927941820345123159 29624021891912730517684739)
      ·
        refine ⟨44436032837869095776527109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29624021891912730517684739 44436032837869095776527109)
        ·
          refine ⟨8331756157100455458098833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44436032837869095776527109 8331756157100455458098833)
          ·
            refine ⟨6248817117825341593574125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8331756157100455458098833 6248817117825341593574125)
            ·
              refine ⟨2343306419184503097590297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6248817117825341593574125 2343306419184503097590297)
              ·
                refine ⟨1757479814388377323192723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2343306419184503097590297 1757479814388377323192723)
                ·
                  refine ⟨2636219721582565984789085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757479814388377323192723 2636219721582565984789085)
                  ·
                    refine ⟨988582395593462244295907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2636219721582565984789085 988582395593462244295907)
                    ·
                      rfl

theorem cell22_2887886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 1, 3].length) (baseStart_2887886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887886 prefixEnd_2887886 := by exact prefixLift 2887886
  have htrace : WordTrace (prefixWord ++ tailWord_2887886) baseStart_2887886 baseEnd_2887886 := by
    simpa [prefixWord, tailWord_2887886, baseEnd_2887886] using wordTrace_append hprefix tailTrace_2887886
  have hstable : (prefixWord ++ tailWord_2887886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887886).length < 2 ^ (prefixWord ++ tailWord_2887886).sum := by decide
  have hdescent : baseEnd_2887886 < baseStart_2887886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887912 : List Nat := [2, 1, 4, 1, 2, 2, 3, 2, 1, 4]
def baseStart_2887912 : Nat := 118140960795 + 2887912 * 2 ^ 59
def prefixEnd_2887912 : Nat := 4983230072969 + 3 ^ 40 * 2887912 * 2
def baseEnd_2887912 : Nat := 988591295924806843145827

theorem tailTrace_2887912 : CollatzResearch.WordTrace tailWord_2887912 prefixEnd_2887912 988591295924806843145827 := by
  unfold tailWord_2887912
  simp only [CollatzResearch.WordTrace]
  refine ⟨52665401956797757473884995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70220535942397009965179993 52665401956797757473884995)
  ·
    refine ⟨78998102935196636210827493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52665401956797757473884995 78998102935196636210827493)
    ·
      refine ⟨14812144300349369289530155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 78998102935196636210827493 14812144300349369289530155)
      ·
        refine ⟨22218216450524053934295233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14812144300349369289530155 22218216450524053934295233)
        ·
          refine ⟨16663662337893040450721425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22218216450524053934295233 16663662337893040450721425)
          ·
            refine ⟨12497746753419780338041069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16663662337893040450721425 12497746753419780338041069)
            ·
              refine ⟨4686655032532417626765401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12497746753419780338041069 4686655032532417626765401)
              ·
                refine ⟨3514991274399313220074051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4686655032532417626765401 3514991274399313220074051)
                ·
                  refine ⟨5272486911598969830111077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3514991274399313220074051 5272486911598969830111077)
                  ·
                    refine ⟨988591295924806843145827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5272486911598969830111077 988591295924806843145827)
                    ·
                      rfl

theorem cell22_2887912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_2887912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887912 prefixEnd_2887912 := by exact prefixLift 2887912
  have htrace : WordTrace (prefixWord ++ tailWord_2887912) baseStart_2887912 baseEnd_2887912 := by
    simpa [prefixWord, tailWord_2887912, baseEnd_2887912] using wordTrace_append hprefix tailTrace_2887912
  have hstable : (prefixWord ++ tailWord_2887912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887912).length < 2 ^ (prefixWord ++ tailWord_2887912).sum := by decide
  have hdescent : baseEnd_2887912 < baseStart_2887912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887944 : List Nat := [2, 1, 3, 2, 3, 1, 4, 2, 4]
def baseStart_2887944 : Nat := 118140960795 + 2887944 * 2 ^ 59
def prefixEnd_2887944 : Nat := 4983230072969 + 3 ^ 40 * 2887944 * 2
def baseEnd_2887944 : Nat := 329534083392923142115243

theorem tailTrace_2887944 : CollatzResearch.WordTrace tailWord_2887944 prefixEnd_2887944 329534083392923142115243 := by
  unfold tailWord_2887944
  simp only [CollatzResearch.WordTrace]
  refine ⟨52665985524739792206467443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70221314032986389608623257 52665985524739792206467443)
  ·
    refine ⟨78998978287109688309701165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52665985524739792206467443 78998978287109688309701165)
    ·
      refine ⟨29624616857666133116137937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 78998978287109688309701165 29624616857666133116137937)
      ·
        refine ⟨22218462643249599837103453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29624616857666133116137937 22218462643249599837103453)
        ·
          refine ⟨8331923491218599938913795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22218462643249599837103453 8331923491218599938913795)
          ·
            refine ⟨12497885236827899908370693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8331923491218599938913795 12497885236827899908370693)
            ·
              refine ⟨2343353481905231232819505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12497885236827899908370693 2343353481905231232819505)
              ·
                refine ⟨1757515111428923424614629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2343353481905231232819505 1757515111428923424614629)
                ·
                  refine ⟨329534083392923142115243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1757515111428923424614629 329534083392923142115243)
                  ·
                    rfl

theorem cell22_2887944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 4, 2, 4].length) (baseStart_2887944 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887944 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887944 prefixEnd_2887944 := by exact prefixLift 2887944
  have htrace : WordTrace (prefixWord ++ tailWord_2887944) baseStart_2887944 baseEnd_2887944 := by
    simpa [prefixWord, tailWord_2887944, baseEnd_2887944] using wordTrace_append hprefix tailTrace_2887944
  have hstable : (prefixWord ++ tailWord_2887944).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887944).length < 2 ^ (prefixWord ++ tailWord_2887944).sum := by decide
  have hdescent : baseEnd_2887944 < baseStart_2887944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2887972 : List Nat := [2, 3, 1, 3, 1, 3, 3, 6]
def baseStart_2887972 : Nat := 118140960795 + 2887972 * 2 ^ 59
def prefixEnd_2887972 : Nat := 4983230072969 + 3 ^ 40 * 2887972 * 2
def baseEnd_2887972 : Nat := 109845759461220742960627

theorem tailTrace_2887972 : CollatzResearch.WordTrace tailWord_2887972 prefixEnd_2887972 109845759461220742960627 := by
  unfold tailWord_2887972
  simp only [CollatzResearch.WordTrace]
  refine ⟨52666496146689072597477085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70221994862252096796636113 52666496146689072597477085)
  ·
    refine ⟨19749936055008402224053907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52666496146689072597477085 19749936055008402224053907)
    ·
      refine ⟨29624904082512603336080861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19749936055008402224053907 29624904082512603336080861)
      ·
        refine ⟨11109339030942226251030323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29624904082512603336080861 11109339030942226251030323)
        ·
          refine ⟨16664008546413339376545485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11109339030942226251030323 16664008546413339376545485)
          ·
            refine ⟨6249003204905002266204557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16664008546413339376545485 6249003204905002266204557)
            ·
              refine ⟨2343376201839375849826709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6249003204905002266204557 2343376201839375849826709)
              ·
                refine ⟨109845759461220742960627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2343376201839375849826709 109845759461220742960627)
                ·
                  rfl

theorem cell22_2887972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 6].length) (baseStart_2887972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2887972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2887972 prefixEnd_2887972 := by exact prefixLift 2887972
  have htrace : WordTrace (prefixWord ++ tailWord_2887972) baseStart_2887972 baseEnd_2887972 := by
    simpa [prefixWord, tailWord_2887972, baseEnd_2887972] using wordTrace_append hprefix tailTrace_2887972
  have hstable : (prefixWord ++ tailWord_2887972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2887972).length < 2 ^ (prefixWord ++ tailWord_2887972).sum := by decide
  have hdescent : baseEnd_2887972 < baseStart_2887972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2887972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888000 : List Nat := [2, 1, 1, 2, 2, 1, 2, 6, 5]
def baseStart_2888000 : Nat := 118140960795 + 2888000 * 2 ^ 59
def prefixEnd_2888000 : Nat := 4983230072969 + 3 ^ 40 * 2888000 * 2
def baseEnd_2888000 : Nat := 329540473374401315648519

theorem tailTrace_2888000 : CollatzResearch.WordTrace tailWord_2888000 prefixEnd_2888000 329540473374401315648519 := by
  unfold tailWord_2888000
  simp only [CollatzResearch.WordTrace]
  refine ⟨52667006768638352988486727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70222675691517803984648969 52667006768638352988486727)
  ·
    refine ⟨79000510152957529482730091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52667006768638352988486727 79000510152957529482730091)
    ·
      refine ⟨118500765229436294224095137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79000510152957529482730091 118500765229436294224095137)
      ·
        refine ⟨88875573922077220668071353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118500765229436294224095137 88875573922077220668071353)
        ·
          refine ⟨66656680441557915501053515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88875573922077220668071353 66656680441557915501053515)
          ·
            refine ⟨99985020662336873251580273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66656680441557915501053515 99985020662336873251580273)
            ·
              refine ⟨74988765496752654938685205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99985020662336873251580273 74988765496752654938685205)
              ·
                refine ⟨3515098382660280700250869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 74988765496752654938685205 3515098382660280700250869)
                ·
                  refine ⟨329540473374401315648519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3515098382660280700250869 329540473374401315648519)
                  ·
                    rfl

theorem cell22_2888000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 6, 5].length) (baseStart_2888000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888000 prefixEnd_2888000 := by exact prefixLift 2888000
  have htrace : WordTrace (prefixWord ++ tailWord_2888000) baseStart_2888000 baseEnd_2888000 := by
    simpa [prefixWord, tailWord_2888000, baseEnd_2888000] using wordTrace_append hprefix tailTrace_2888000
  have hstable : (prefixWord ++ tailWord_2888000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888000).length < 2 ^ (prefixWord ++ tailWord_2888000).sum := by decide
  have hdescent : baseEnd_2888000 < baseStart_2888000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888060 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 5, 5]
def baseStart_2888060 : Nat := 118140960795 + 2888060 * 2 ^ 59
def prefixEnd_2888060 : Nat := 4983230072969 + 3 ^ 40 * 2888060 * 2
def baseEnd_2888060 : Nat := 988641959349383790445373

theorem tailTrace_2888060 : CollatzResearch.WordTrace tailWord_2888060 prefixEnd_2888060 988641959349383790445373 := by
  unfold tailWord_2888060
  simp only [CollatzResearch.WordTrace]
  refine ⟨52668100958529668112078817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70224134611372890816105089 52668100958529668112078817)
  ·
    refine ⟨39501075718897251084059113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52668100958529668112078817 39501075718897251084059113)
    ·
      refine ⟨29625806789172938313044335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39501075718897251084059113 29625806789172938313044335)
      ·
        refine ⟨44438710183759407469566503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29625806789172938313044335 44438710183759407469566503)
        ·
          refine ⟨66658065275639111204349755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44438710183759407469566503 66658065275639111204349755)
          ·
            refine ⟨99987097913458666806524633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66658065275639111204349755 99987097913458666806524633)
            ·
              refine ⟨74990323435094000104893475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 99987097913458666806524633 74990323435094000104893475)
              ·
                refine ⟨112485485152641000157340213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 74990323435094000104893475 112485485152641000157340213)
                ·
                  refine ⟨10545514233060093764750645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112485485152641000157340213 10545514233060093764750645)
                  ·
                    refine ⟨988641959349383790445373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10545514233060093764750645 988641959349383790445373)
                    ·
                      rfl

theorem cell22_2888060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 5, 5].length) (baseStart_2888060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888060 prefixEnd_2888060 := by exact prefixLift 2888060
  have htrace : WordTrace (prefixWord ++ tailWord_2888060) baseStart_2888060 baseEnd_2888060 := by
    simpa [prefixWord, tailWord_2888060, baseEnd_2888060] using wordTrace_append hprefix tailTrace_2888060
  have hstable : (prefixWord ++ tailWord_2888060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888060).length < 2 ^ (prefixWord ++ tailWord_2888060).sum := by decide
  have hdescent : baseEnd_2888060 < baseStart_2888060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888094 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 3, 5]
def baseStart_2888094 : Nat := 118140960795 + 2888094 * 2 ^ 59
def prefixEnd_2888094 : Nat := 4983230072969 + 3 ^ 40 * 2888094 * 2
def baseEnd_2888094 : Nat := 988653598244219035095269

theorem tailTrace_2888094 : CollatzResearch.WordTrace tailWord_2888094 prefixEnd_2888094 988653598244219035095269 := by
  unfold tailWord_2888094
  simp only [CollatzResearch.WordTrace]
  refine ⟨13167180249867020003861917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70224961332624106687263557 13167180249867020003861917)
  ·
    refine ⟨4937692593700132501448219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13167180249867020003861917 4937692593700132501448219)
    ·
      refine ⟨7406538890550198752172329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4937692593700132501448219 7406538890550198752172329)
      ·
        refine ⟨5554904167912649064129247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7406538890550198752172329 5554904167912649064129247)
        ·
          refine ⟨8332356251868973596193871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5554904167912649064129247 8332356251868973596193871)
          ·
            refine ⟨12498534377803460394290807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8332356251868973596193871 12498534377803460394290807)
            ·
              refine ⟨18747801566705190591436211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12498534377803460394290807 18747801566705190591436211)
              ·
                refine ⟨28121702350057785887154317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18747801566705190591436211 28121702350057785887154317)
                ·
                  refine ⟨10545638381271669707682869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28121702350057785887154317 10545638381271669707682869)
                  ·
                    refine ⟨988653598244219035095269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10545638381271669707682869 988653598244219035095269)
                    ·
                      rfl

theorem cell22_2888094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_2888094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888094 prefixEnd_2888094 := by exact prefixLift 2888094
  have htrace : WordTrace (prefixWord ++ tailWord_2888094) baseStart_2888094 baseEnd_2888094 := by
    simpa [prefixWord, tailWord_2888094, baseEnd_2888094] using wordTrace_append hprefix tailTrace_2888094
  have hstable : (prefixWord ++ tailWord_2888094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888094).length < 2 ^ (prefixWord ++ tailWord_2888094).sum := by decide
  have hdescent : baseEnd_2888094 < baseStart_2888094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888122 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 7, 3]
def baseStart_2888122 : Nat := 118140960795 + 2888122 * 2 ^ 59
def prefixEnd_2888122 : Nat := 4983230072969 + 3 ^ 40 * 2888122 * 2
def baseEnd_2888122 : Nat := 988663183216436295395183

theorem tailTrace_2888122 : CollatzResearch.WordTrace tailWord_2888122 prefixEnd_2888122 988663183216436295395183 := by
  unfold tailWord_2888122
  simp only [CollatzResearch.WordTrace]
  refine ⟨26334615810708680203228655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70225642161889813875276413 26334615810708680203228655)
  ·
    refine ⟨39501923716063020304842983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26334615810708680203228655 39501923716063020304842983)
    ·
      refine ⟨59252885574094530457264475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39501923716063020304842983 59252885574094530457264475)
      ·
        refine ⟨88879328361141795685896713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59252885574094530457264475 88879328361141795685896713)
        ·
          refine ⟨66659496270856346764422535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88879328361141795685896713 66659496270856346764422535)
          ·
            refine ⟨99989244406284520146633803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66659496270856346764422535 99989244406284520146633803)
            ·
              refine ⟨149983866609426780219950705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99989244406284520146633803 149983866609426780219950705)
              ·
                refine ⟨112487899957070085164963029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 149983866609426780219950705 112487899957070085164963029)
                ·
                  refine ⟨2636435155243830121053821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 112487899957070085164963029 2636435155243830121053821)
                  ·
                    refine ⟨988663183216436295395183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2636435155243830121053821 988663183216436295395183)
                    ·
                      rfl

theorem cell22_2888122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 7, 3].length) (baseStart_2888122 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888122 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888122 prefixEnd_2888122 := by exact prefixLift 2888122
  have htrace : WordTrace (prefixWord ++ tailWord_2888122) baseStart_2888122 baseEnd_2888122 := by
    simpa [prefixWord, tailWord_2888122, baseEnd_2888122] using wordTrace_append hprefix tailTrace_2888122
  have hstable : (prefixWord ++ tailWord_2888122).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888122).length < 2 ^ (prefixWord ++ tailWord_2888122).sum := by decide
  have hdescent : baseEnd_2888122 < baseStart_2888122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888124 : List Nat := [2, 2, 2, 4, 1, 3, 1, 7]
def baseStart_2888124 : Nat := 118140960795 + 2888124 * 2 ^ 59
def prefixEnd_2888124 : Nat := 4983230072969 + 3 ^ 40 * 2888124 * 2
def baseEnd_2888124 : Nat := 109851540873034328538353

theorem tailTrace_2888124 : CollatzResearch.WordTrace tailWord_2888124 prefixEnd_2888124 109851540873034328538353 := by
  unfold tailWord_2888124
  simp only [CollatzResearch.WordTrace]
  refine ⟨52669268094413737577243713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70225690792551650102991617 52669268094413737577243713)
  ·
    refine ⟨39501951070810303182932785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52669268094413737577243713 39501951070810303182932785)
    ·
      refine ⟨29626463303107727387199589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39501951070810303182932785 29626463303107727387199589)
      ·
        refine ⟨5554961869332698885099923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29626463303107727387199589 5554961869332698885099923)
        ·
          refine ⟨8332442803999048327649885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5554961869332698885099923 8332442803999048327649885)
          ·
            refine ⟨3124666051499643122868707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8332442803999048327649885 3124666051499643122868707)
            ·
              refine ⟨4686999077249464684303061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3124666051499643122868707 4686999077249464684303061)
              ·
                refine ⟨109851540873034328538353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4686999077249464684303061 109851540873034328538353)
                ·
                  rfl

theorem cell22_2888124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 7].length) (baseStart_2888124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888124 prefixEnd_2888124 := by exact prefixLift 2888124
  have htrace : WordTrace (prefixWord ++ tailWord_2888124) baseStart_2888124 baseEnd_2888124 := by
    simpa [prefixWord, tailWord_2888124, baseEnd_2888124] using wordTrace_append hprefix tailTrace_2888124
  have hstable : (prefixWord ++ tailWord_2888124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888124).length < 2 ^ (prefixWord ++ tailWord_2888124).sum := by decide
  have hdescent : baseEnd_2888124 < baseStart_2888124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888162 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 2, 3]
def baseStart_2888162 : Nat := 118140960795 + 2888162 * 2 ^ 59
def prefixEnd_2888162 : Nat := 4983230072969 + 3 ^ 40 * 2888162 * 2
def baseEnd_2888162 : Nat := 988676876033889524395061

theorem tailTrace_2888162 : CollatzResearch.WordTrace tailWord_2888162 prefixEnd_2888162 988676876033889524395061 := by
  unfold tailWord_2888162
  simp only [CollatzResearch.WordTrace]
  refine ⟨26334980540672451911092685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70226614775126538429580493 26334980540672451911092685)
  ·
    refine ⟨9875617702752169466659757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26334980540672451911092685 9875617702752169466659757)
    ·
      refine ⟨3703356638532063549997409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9875617702752169466659757 3703356638532063549997409)
      ·
        refine ⟨2777517478899047662498057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3703356638532063549997409 2777517478899047662498057)
        ·
          refine ⟨2083138109174285746873543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2777517478899047662498057 2083138109174285746873543)
          ·
            refine ⟨3124707163761428620310315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083138109174285746873543 3124707163761428620310315)
            ·
              refine ⟨4687060745642142930465473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3124707163761428620310315 4687060745642142930465473)
              ·
                refine ⟨3515295559231607197849105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687060745642142930465473 3515295559231607197849105)
                ·
                  refine ⟨2636471669423705398386829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3515295559231607197849105 2636471669423705398386829)
                  ·
                    refine ⟨988676876033889524395061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2636471669423705398386829 988676876033889524395061)
                    ·
                      rfl

theorem cell22_2888162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_2888162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888162 prefixEnd_2888162 := by exact prefixLift 2888162
  have htrace : WordTrace (prefixWord ++ tailWord_2888162) baseStart_2888162 baseEnd_2888162 := by
    simpa [prefixWord, tailWord_2888162, baseEnd_2888162] using wordTrace_append hprefix tailTrace_2888162
  have hstable : (prefixWord ++ tailWord_2888162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888162).length < 2 ^ (prefixWord ++ tailWord_2888162).sum := by decide
  have hdescent : baseEnd_2888162 < baseStart_2888162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888167 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 4, 5]
def baseStart_2888167 : Nat := 118140960795 + 2888167 * 2 ^ 59
def prefixEnd_2888167 : Nat := 4983230072969 + 3 ^ 40 * 2888167 * 2
def baseEnd_2888167 : Nat := 988678587636071178020045

theorem tailTrace_2888167 : CollatzResearch.WordTrace tailWord_2888167 prefixEnd_2888167 988678587636071178020045 := by
  unfold tailWord_2888167
  simp only [CollatzResearch.WordTrace]
  refine ⟨105340104527671693498302755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70226736351781128998868503 105340104527671693498302755)
  ·
    refine ⟨158010156791507540247454133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105340104527671693498302755 158010156791507540247454133)
    ·
      refine ⟨14813452199203831898198825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158010156791507540247454133 14813452199203831898198825)
      ·
        refine ⟨11110089149402873923649119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14813452199203831898198825 11110089149402873923649119)
        ·
          refine ⟨16665133724104310885473679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11110089149402873923649119 16665133724104310885473679)
          ·
            refine ⟨24997700586156466328210519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16665133724104310885473679 24997700586156466328210519)
            ·
              refine ⟨37496550879234699492315779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24997700586156466328210519 37496550879234699492315779)
              ·
                refine ⟨56244826318852049238473669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37496550879234699492315779 56244826318852049238473669)
                ·
                  refine ⟨10545904934784759232213813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56244826318852049238473669 10545904934784759232213813)
                  ·
                    refine ⟨988678587636071178020045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10545904934784759232213813 988678587636071178020045)
                    ·
                      rfl

theorem cell22_2888167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_2888167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888167 prefixEnd_2888167 := by exact prefixLift 2888167
  have htrace : WordTrace (prefixWord ++ tailWord_2888167) baseStart_2888167 baseEnd_2888167 := by
    simpa [prefixWord, tailWord_2888167, baseEnd_2888167] using wordTrace_append hprefix tailTrace_2888167
  have hstable : (prefixWord ++ tailWord_2888167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888167).length < 2 ^ (prefixWord ++ tailWord_2888167).sum := by decide
  have hdescent : baseEnd_2888167 < baseStart_2888167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888173 : List Nat := [1, 5, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_2888173 : Nat := 118140960795 + 2888173 * 2 ^ 59
def prefixEnd_2888173 : Nat := 4983230072969 + 3 ^ 40 * 2888173 * 2
def baseEnd_2888173 : Nat := 988680641558689162370027

theorem tailTrace_2888173 : CollatzResearch.WordTrace tailWord_2888173 prefixEnd_2888173 988680641558689162370027 := by
  unfold tailWord_2888173
  simp only [CollatzResearch.WordTrace]
  refine ⟨105340323365649956523021173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70226882243766637682014115 105340323365649956523021173)
  ·
    refine ⟨9875655315529683424033235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105340323365649956523021173 9875655315529683424033235)
    ·
      refine ⟨14813482973294525136049853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9875655315529683424033235 14813482973294525136049853)
      ·
        refine ⟨5555056114985446926018695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14813482973294525136049853 5555056114985446926018695)
        ·
          refine ⟨8332584172478170389028043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5555056114985446926018695 8332584172478170389028043)
          ·
            refine ⟨12498876258717255583542065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8332584172478170389028043 12498876258717255583542065)
            ·
              refine ⟨9374157194037941687656549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12498876258717255583542065 9374157194037941687656549)
              ·
                refine ⟨1757654473882114066435603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9374157194037941687656549 1757654473882114066435603)
                ·
                  refine ⟨2636481710823171099653405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1757654473882114066435603 2636481710823171099653405)
                  ·
                    refine ⟨988680641558689162370027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2636481710823171099653405 988680641558689162370027)
                    ·
                      rfl

theorem cell22_2888173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_2888173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888173 prefixEnd_2888173 := by exact prefixLift 2888173
  have htrace : WordTrace (prefixWord ++ tailWord_2888173) baseStart_2888173 baseEnd_2888173 := by
    simpa [prefixWord, tailWord_2888173, baseEnd_2888173] using wordTrace_append hprefix tailTrace_2888173
  have hstable : (prefixWord ++ tailWord_2888173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888173).length < 2 ^ (prefixWord ++ tailWord_2888173).sum := by decide
  have hdescent : baseEnd_2888173 < baseStart_2888173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888197 : List Nat := [1, 3, 1, 1, 2, 2, 4, 2, 6]
def baseStart_2888197 : Nat := 118140960795 + 2888197 * 2 ^ 59
def prefixEnd_2888197 : Nat := 4983230072969 + 3 ^ 40 * 2888197 * 2
def baseEnd_2888197 : Nat := 329562952416387033256651

theorem tailTrace_2888197 : CollatzResearch.WordTrace tailWord_2888197 prefixEnd_2888197 329562952416387033256651 := by
  unfold tailWord_2888197
  simp only [CollatzResearch.WordTrace]
  refine ⟨105341198717563008621894845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70227465811708672414596563 105341198717563008621894845)
  ·
    refine ⟨39502949519086128233210567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105341198717563008621894845 39502949519086128233210567)
    ·
      refine ⟨59254424278629192349815851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39502949519086128233210567 59254424278629192349815851)
      ·
        refine ⟨88881636417943788524723777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59254424278629192349815851 88881636417943788524723777)
        ·
          refine ⟨66661227313457841393542833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88881636417943788524723777 66661227313457841393542833)
          ·
            refine ⟨49995920485093381045157125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66661227313457841393542833 49995920485093381045157125)
            ·
              refine ⟨9374235090955008945966961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49995920485093381045157125 9374235090955008945966961)
              ·
                refine ⟨7030676318216256709475221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9374235090955008945966961 7030676318216256709475221)
                ·
                  refine ⟨329562952416387033256651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7030676318216256709475221 329562952416387033256651)
                  ·
                    rfl

theorem cell22_2888197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_2888197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888197 prefixEnd_2888197 := by exact prefixLift 2888197
  have htrace : WordTrace (prefixWord ++ tailWord_2888197) baseStart_2888197 baseEnd_2888197 := by
    simpa [prefixWord, tailWord_2888197, baseEnd_2888197] using wordTrace_append hprefix tailTrace_2888197
  have hstable : (prefixWord ++ tailWord_2888197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888197).length < 2 ^ (prefixWord ++ tailWord_2888197).sum := by decide
  have hdescent : baseEnd_2888197 < baseStart_2888197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888229 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 4, 3]
def baseStart_2888229 : Nat := 118140960795 + 2888229 * 2 ^ 59
def prefixEnd_2888229 : Nat := 4983230072969 + 3 ^ 40 * 2888229 * 2
def baseEnd_2888229 : Nat := 988699811503123682969855

theorem tailTrace_2888229 : CollatzResearch.WordTrace tailWord_2888229 prefixEnd_2888229 988699811503123682969855 := by
  unfold tailWord_2888229
  simp only [CollatzResearch.WordTrace]
  refine ⟨105342365853447078087059741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70228243902298052058039827 105342365853447078087059741)
  ·
    refine ⟨39503387195042654282647403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105342365853447078087059741 39503387195042654282647403)
    ·
      refine ⟨59255080792563981423971105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39503387195042654282647403 59255080792563981423971105)
      ·
        refine ⟨44441310594422986067978329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59255080792563981423971105 44441310594422986067978329)
        ·
          refine ⟨33330982945817239550983747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44441310594422986067978329 33330982945817239550983747)
          ·
            refine ⟨49996474418725859326475621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33330982945817239550983747 49996474418725859326475621)
            ·
              refine ⟨9374338953511098623714179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 49996474418725859326475621 9374338953511098623714179)
              ·
                refine ⟨14061508430266647935571269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9374338953511098623714179 14061508430266647935571269)
                ·
                  refine ⟨2636532830674996487919613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14061508430266647935571269 2636532830674996487919613)
                  ·
                    refine ⟨988699811503123682969855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2636532830674996487919613 988699811503123682969855)
                    ·
                      rfl

theorem cell22_2888229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 4, 3].length) (baseStart_2888229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888229 prefixEnd_2888229 := by exact prefixLift 2888229
  have htrace : WordTrace (prefixWord ++ tailWord_2888229) baseStart_2888229 baseEnd_2888229 := by
    simpa [prefixWord, tailWord_2888229, baseEnd_2888229] using wordTrace_append hprefix tailTrace_2888229
  have hstable : (prefixWord ++ tailWord_2888229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888229).length < 2 ^ (prefixWord ++ tailWord_2888229).sum := by decide
  have hdescent : baseEnd_2888229 < baseStart_2888229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888237 : List Nat := [1, 5, 4, 1, 1, 2, 2, 1, 5]
def baseStart_2888237 : Nat := 118140960795 + 2888237 * 2 ^ 59
def prefixEnd_2888237 : Nat := 4983230072969 + 3 ^ 40 * 2888237 * 2
def baseEnd_2888237 : Nat := 329567516688871442923277

theorem tailTrace_2888237 : CollatzResearch.WordTrace tailWord_2888237 prefixEnd_2888237 329567516688871442923277 := by
  unfold tailWord_2888237
  simp only [CollatzResearch.WordTrace]
  refine ⟨105342657637418095453350965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70228438424945396968900643 105342657637418095453350965)
  ·
    refine ⟨9875874153507946448751653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105342657637418095453350965 9875874153507946448751653)
    ·
      refine ⟨1851726403782739959140935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9875874153507946448751653 1851726403782739959140935)
      ·
        refine ⟨2777589605674109938711403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1851726403782739959140935 2777589605674109938711403)
        ·
          refine ⟨4166384408511164908067105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2777589605674109938711403 4166384408511164908067105)
          ·
            refine ⟨3124788306383373681050329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4166384408511164908067105 3124788306383373681050329)
            ·
              refine ⟨2343591229787530260787747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3124788306383373681050329 2343591229787530260787747)
              ·
                refine ⟨3515386844681295391181621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343591229787530260787747 3515386844681295391181621)
                ·
                  refine ⟨329567516688871442923277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3515386844681295391181621 329567516688871442923277)
                  ·
                    rfl

theorem cell22_2888237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_2888237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888237 prefixEnd_2888237 := by exact prefixLift 2888237
  have htrace : WordTrace (prefixWord ++ tailWord_2888237) baseStart_2888237 baseEnd_2888237 := by
    simpa [prefixWord, tailWord_2888237, baseEnd_2888237] using wordTrace_append hprefix tailTrace_2888237
  have hstable : (prefixWord ++ tailWord_2888237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888237).length < 2 ^ (prefixWord ++ tailWord_2888237).sum := by decide
  have hdescent : baseEnd_2888237 < baseStart_2888237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888242 : List Nat := [3, 2, 1, 1, 2, 1, 3, 9]
def baseStart_2888242 : Nat := 118140960795 + 2888242 * 2 ^ 59
def prefixEnd_2888242 : Nat := 4983230072969 + 3 ^ 40 * 2888242 * 2
def baseEnd_2888242 : Nat := 109856029074310664710535

theorem tailTrace_2888242 : CollatzResearch.WordTrace tailWord_2888242 prefixEnd_2888242 109856029074310664710535 := by
  unfold tailWord_2888242
  simp only [CollatzResearch.WordTrace]
  refine ⟨26335710000599995326820745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70228560001599987538188653 26335710000599995326820745)
  ·
    refine ⟨19751782500449996495115559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26335710000599995326820745 19751782500449996495115559)
    ·
      refine ⟨29627673750674994742673339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19751782500449996495115559 29627673750674994742673339)
      ·
        refine ⟨44441510626012492114010009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29627673750674994742673339 44441510626012492114010009)
        ·
          refine ⟨33331132969509369085507507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44441510626012492114010009 33331132969509369085507507)
          ·
            refine ⟨49996699454264053628261261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33331132969509369085507507 49996699454264053628261261)
            ·
              refine ⟨18748762295349020110597973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49996699454264053628261261 18748762295349020110597973)
              ·
                refine ⟨109856029074310664710535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 18748762295349020110597973 109856029074310664710535)
                ·
                  rfl

theorem cell22_2888242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 9].length) (baseStart_2888242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888242 prefixEnd_2888242 := by exact prefixLift 2888242
  have htrace : WordTrace (prefixWord ++ tailWord_2888242) baseStart_2888242 baseEnd_2888242 := by
    simpa [prefixWord, tailWord_2888242, baseEnd_2888242] using wordTrace_append hprefix tailTrace_2888242
  have hstable : (prefixWord ++ tailWord_2888242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888242).length < 2 ^ (prefixWord ++ tailWord_2888242).sum := by decide
  have hdescent : baseEnd_2888242 < baseStart_2888242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888287 : List Nat := [1, 1, 2, 3, 1, 1, 1, 5, 7]
def baseStart_2888287 : Nat := 118140960795 + 2888287 * 2 ^ 59
def prefixEnd_2888287 : Nat := 4983230072969 + 3 ^ 40 * 2888287 * 2
def baseEnd_2888287 : Nat := 329573222029476955006559

theorem tailTrace_2888287 : CollatzResearch.WordTrace tailWord_2888287 prefixEnd_2888287 329573222029476955006559 := by
  unfold tailWord_2888287
  simp only [CollatzResearch.WordTrace]
  refine ⟨105344481287236953992671115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70229654191491302661780743 105344481287236953992671115)
  ·
    refine ⟨158016721930855430989006673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105344481287236953992671115 158016721930855430989006673)
    ·
      refine ⟨118512541448141573241755005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158016721930855430989006673 118512541448141573241755005)
      ·
        refine ⟨44442203043053089965658127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118512541448141573241755005 44442203043053089965658127)
        ·
          refine ⟨66663304564579634948487191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44442203043053089965658127 66663304564579634948487191)
          ·
            refine ⟨99994956846869452422730787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66663304564579634948487191 99994956846869452422730787)
            ·
              refine ⟨149992435270304178634096181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 99994956846869452422730787 149992435270304178634096181)
              ·
                refine ⟨14061790806591016746946517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 149992435270304178634096181 14061790806591016746946517)
                ·
                  refine ⟨329573222029476955006559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14061790806591016746946517 329573222029476955006559)
                  ·
                    rfl

theorem cell22_2888287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 5, 7].length) (baseStart_2888287 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888287 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888287 prefixEnd_2888287 := by exact prefixLift 2888287
  have htrace : WordTrace (prefixWord ++ tailWord_2888287) baseStart_2888287 baseEnd_2888287 := by
    simpa [prefixWord, tailWord_2888287, baseEnd_2888287] using wordTrace_append hprefix tailTrace_2888287
  have hstable : (prefixWord ++ tailWord_2888287).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888287).length < 2 ^ (prefixWord ++ tailWord_2888287).sum := by decide
  have hdescent : baseEnd_2888287 < baseStart_2888287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888338 : List Nat := [3, 2, 3, 1, 2, 3, 1, 2, 5]
def baseStart_2888338 : Nat := 118140960795 + 2888338 * 2 ^ 59
def prefixEnd_2888338 : Nat := 4983230072969 + 3 ^ 40 * 2888338 * 2
def baseEnd_2888338 : Nat := 329579041476894577331507

theorem tailTrace_2888338 : CollatzResearch.WordTrace tailWord_2888338 prefixEnd_2888338 329579041476894577331507 := by
  unfold tailWord_2888338
  simp only [CollatzResearch.WordTrace]
  refine ⟨26336585352513047425694417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70230894273368126468518445 26336585352513047425694417)
  ·
    refine ⟨19752439014384785569270813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26336585352513047425694417 19752439014384785569270813)
    ·
      refine ⟨7407164630394294588476555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19752439014384785569270813 7407164630394294588476555)
      ·
        refine ⟨11110746945591441882714833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7407164630394294588476555 11110746945591441882714833)
        ·
          refine ⟨8333060209193581412036125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11110746945591441882714833 8333060209193581412036125)
          ·
            refine ⟨3124897578447593029513547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8333060209193581412036125 3124897578447593029513547)
            ·
              refine ⟨4687346367671389544270321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3124897578447593029513547 4687346367671389544270321)
              ·
                refine ⟨3515509775753542158202741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687346367671389544270321 3515509775753542158202741)
                ·
                  refine ⟨329579041476894577331507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3515509775753542158202741 329579041476894577331507)
                  ·
                    rfl

theorem cell22_2888338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 1, 2, 5].length) (baseStart_2888338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888338 prefixEnd_2888338 := by exact prefixLift 2888338
  have htrace : WordTrace (prefixWord ++ tailWord_2888338) baseStart_2888338 baseEnd_2888338 := by
    simpa [prefixWord, tailWord_2888338, baseEnd_2888338] using wordTrace_append hprefix tailTrace_2888338
  have hstable : (prefixWord ++ tailWord_2888338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888338).length < 2 ^ (prefixWord ++ tailWord_2888338).sum := by decide
  have hdescent : baseEnd_2888338 < baseStart_2888338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888349 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 6]
def baseStart_2888349 : Nat := 118140960795 + 2888349 * 2 ^ 59
def prefixEnd_2888349 : Nat := 4983230072969 + 3 ^ 40 * 2888349 * 2
def baseEnd_2888349 : Nat := 329580296651827789989829

theorem tailTrace_2888349 : CollatzResearch.WordTrace tailWord_2888349 prefixEnd_2888349 329580296651827789989829 := by
  unfold tailWord_2888349
  simp only [CollatzResearch.WordTrace]
  refine ⟨105346742613012338581428101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70231161742008225720952067 105346742613012338581428101)
  ·
    refine ⟨19752514239939813484017769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105346742613012338581428101 19752514239939813484017769)
    ·
      refine ⟨14814385679954860113013327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19752514239939813484017769 14814385679954860113013327)
      ·
        refine ⟨22221578519932290169519991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14814385679954860113013327 22221578519932290169519991)
        ·
          refine ⟨33332367779898435254279987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22221578519932290169519991 33332367779898435254279987)
          ·
            refine ⟨49998551669847652881419981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33332367779898435254279987 49998551669847652881419981)
            ·
              refine ⟨18749456876192869830532493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 49998551669847652881419981 18749456876192869830532493)
              ·
                refine ⟨7031046328572326186449685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18749456876192869830532493 7031046328572326186449685)
                ·
                  refine ⟨329580296651827789989829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7031046328572326186449685 329580296651827789989829)
                  ·
                    rfl

theorem cell22_2888349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 6].length) (baseStart_2888349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888349 prefixEnd_2888349 := by exact prefixLift 2888349
  have htrace : WordTrace (prefixWord ++ tailWord_2888349) baseStart_2888349 baseEnd_2888349 := by
    simpa [prefixWord, tailWord_2888349, baseEnd_2888349] using wordTrace_append hprefix tailTrace_2888349
  have hstable : (prefixWord ++ tailWord_2888349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888349).length < 2 ^ (prefixWord ++ tailWord_2888349).sum := by decide
  have hdescent : baseEnd_2888349 < baseStart_2888349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888381 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 4, 3]
def baseStart_2888381 : Nat := 118140960795 + 2888381 * 2 ^ 59
def prefixEnd_2888381 : Nat := 4983230072969 + 3 ^ 40 * 2888381 * 2
def baseEnd_2888381 : Nat := 988751844209445953169389

theorem tailTrace_2888381 : CollatzResearch.WordTrace tailWord_2888381 prefixEnd_2888381 988751844209445953169389 := by
  unfold tailWord_2888381
  simp only [CollatzResearch.WordTrace]
  refine ⟨105347909748896408046592997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70231939832597605364395331 105347909748896408046592997)
  ·
    refine ⟨19752733077918076508736187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105347909748896408046592997 19752733077918076508736187)
    ·
      refine ⟨29629099616877114763104281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19752733077918076508736187 29629099616877114763104281)
      ·
        refine ⟨22221824712657836072328211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29629099616877114763104281 22221824712657836072328211)
        ·
          refine ⟨33332737068986754108492317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22221824712657836072328211 33332737068986754108492317)
          ·
            refine ⟨12499776400870032790684619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33332737068986754108492317 12499776400870032790684619)
            ·
              refine ⟨18749664601305049186026929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12499776400870032790684619 18749664601305049186026929)
              ·
                refine ⟨14062248450978786889520197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18749664601305049186026929 14062248450978786889520197)
                ·
                  refine ⟨2636671584558522541785037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14062248450978786889520197 2636671584558522541785037)
                  ·
                    refine ⟨988751844209445953169389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2636671584558522541785037 988751844209445953169389)
                    ·
                      rfl

theorem cell22_2888381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_2888381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888381 prefixEnd_2888381 := by exact prefixLift 2888381
  have htrace : WordTrace (prefixWord ++ tailWord_2888381) baseStart_2888381 baseEnd_2888381 := by
    simpa [prefixWord, tailWord_2888381, baseEnd_2888381] using wordTrace_append hprefix tailTrace_2888381
  have hstable : (prefixWord ++ tailWord_2888381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888381).length < 2 ^ (prefixWord ++ tailWord_2888381).sum := by decide
  have hdescent : baseEnd_2888381 < baseStart_2888381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888383 : List Nat := [1, 1, 2, 2, 2, 6, 1, 3, 4]
def baseStart_2888383 : Nat := 118140960795 + 2888383 * 2 ^ 59
def prefixEnd_2888383 : Nat := 4983230072969 + 3 ^ 40 * 2888383 * 2
def baseEnd_2888383 : Nat := 329584176283439538206461

theorem tailTrace_2888383 : CollatzResearch.WordTrace tailWord_2888383 prefixEnd_2888383 329584176283439538206461 := by
  unfold tailWord_2888383
  simp only [CollatzResearch.WordTrace]
  refine ⟨105347982694889162388165803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70231988463259441592110535 105347982694889162388165803)
  ·
    refine ⟨158021974042333743582248705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105347982694889162388165803 158021974042333743582248705)
    ·
      refine ⟨118516480531750307686686529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158021974042333743582248705 118516480531750307686686529)
      ·
        refine ⟨88887360398812730765014897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118516480531750307686686529 88887360398812730765014897)
        ·
          refine ⟨66665520299109548073761173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88887360398812730765014897 66665520299109548073761173)
          ·
            refine ⟨3124946264020760065957555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66665520299109548073761173 3124946264020760065957555)
            ·
              refine ⟨4687419396031140098936333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3124946264020760065957555 4687419396031140098936333)
              ·
                refine ⟨1757782273511677537101125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4687419396031140098936333 1757782273511677537101125)
                ·
                  refine ⟨329584176283439538206461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1757782273511677537101125 329584176283439538206461)
                  ·
                    rfl

theorem cell22_2888383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 3, 4].length) (baseStart_2888383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888383 prefixEnd_2888383 := by exact prefixLift 2888383
  have htrace : WordTrace (prefixWord ++ tailWord_2888383) baseStart_2888383 baseEnd_2888383 := by
    simpa [prefixWord, tailWord_2888383, baseEnd_2888383] using wordTrace_append hprefix tailTrace_2888383
  have hstable : (prefixWord ++ tailWord_2888383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888383).length < 2 ^ (prefixWord ++ tailWord_2888383).sum := by decide
  have hdescent : baseEnd_2888383 < baseStart_2888383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888394 : List Nat := [3, 1, 2, 1, 4, 1, 10]
def baseStart_2888394 : Nat := 118140960795 + 2888394 * 2 ^ 59
def prefixEnd_2888394 : Nat := 4983230072969 + 3 ^ 40 * 2888394 * 2
def baseEnd_2888394 : Nat := 36620603495374750096087

theorem tailTrace_2888394 : CollatzResearch.WordTrace tailWord_2888394 prefixEnd_2888394 36620603495374750096087 := by
  unfold tailWord_2888394
  simp only [CollatzResearch.WordTrace]
  refine ⟨26337095974462327816704059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70232255931899540844544157 26337095974462327816704059)
  ·
    refine ⟨39505643961693491725056089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26337095974462327816704059 39505643961693491725056089)
    ·
      refine ⟨29629232971270118793792067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39505643961693491725056089 29629232971270118793792067)
      ·
        refine ⟨44443849456905178190688101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29629232971270118793792067 44443849456905178190688101)
        ·
          refine ⟨8333221773169720910754019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44443849456905178190688101 8333221773169720910754019)
          ·
            refine ⟨12499832659754581366131029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8333221773169720910754019 12499832659754581366131029)
            ·
              refine ⟨36620603495374750096087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 12499832659754581366131029 36620603495374750096087)
              ·
                rfl

theorem cell22_2888394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 10].length) (baseStart_2888394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888394 prefixEnd_2888394 := by exact prefixLift 2888394
  have htrace : WordTrace (prefixWord ++ tailWord_2888394) baseStart_2888394 baseEnd_2888394 := by
    simpa [prefixWord, tailWord_2888394, baseEnd_2888394] using wordTrace_append hprefix tailTrace_2888394
  have hstable : (prefixWord ++ tailWord_2888394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888394).length < 2 ^ (prefixWord ++ tailWord_2888394).sum := by decide
  have hdescent : baseEnd_2888394 < baseStart_2888394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888396 : List Nat := [2, 2, 1, 5, 1, 1, 1, 1, 4, 4]
def baseStart_2888396 : Nat := 118140960795 + 2888396 * 2 ^ 59
def prefixEnd_2888396 : Nat := 4983230072969 + 3 ^ 40 * 2888396 * 2
def baseEnd_2888396 : Nat := 988756979015990914044343

theorem tailTrace_2888396 : CollatzResearch.WordTrace tailWord_2888396 prefixEnd_2888396 988756979015990914044343 := by
  unfold tailWord_2888396
  simp only [CollatzResearch.WordTrace]
  refine ⟨52674228421921032804194521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70232304562561377072259361 52674228421921032804194521)
  ·
    refine ⟨39505671316440774603145891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52674228421921032804194521 39505671316440774603145891)
    ·
      refine ⟨59258506974661161904718837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39505671316440774603145891 59258506974661161904718837)
      ·
        refine ⟨5555485028874483928567391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59258506974661161904718837 5555485028874483928567391)
        ·
          refine ⟨8333227543311725892851087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5555485028874483928567391 8333227543311725892851087)
          ·
            refine ⟨12499841314967588839276631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8333227543311725892851087 12499841314967588839276631)
            ·
              refine ⟨18749761972451383258914947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12499841314967588839276631 18749761972451383258914947)
              ·
                refine ⟨28124642958677074888372421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18749761972451383258914947 28124642958677074888372421)
                ·
                  refine ⟨5273370554751951541569829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28124642958677074888372421 5273370554751951541569829)
                  ·
                    refine ⟨988756979015990914044343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5273370554751951541569829 988756979015990914044343)
                    ·
                      rfl

theorem cell22_2888396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 4, 4].length) (baseStart_2888396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888396 prefixEnd_2888396 := by exact prefixLift 2888396
  have htrace : WordTrace (prefixWord ++ tailWord_2888396) baseStart_2888396 baseEnd_2888396 := by
    simpa [prefixWord, tailWord_2888396, baseEnd_2888396] using wordTrace_append hprefix tailTrace_2888396
  have hstable : (prefixWord ++ tailWord_2888396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888396).length < 2 ^ (prefixWord ++ tailWord_2888396).sum := by decide
  have hdescent : baseEnd_2888396 < baseStart_2888396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888415 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 2, 3]
def baseStart_2888415 : Nat := 118140960795 + 2888415 * 2 ^ 59
def prefixEnd_2888415 : Nat := 4983230072969 + 3 ^ 40 * 2888415 * 2
def baseEnd_2888415 : Nat := 988763483104281197819285

theorem tailTrace_2888415 : CollatzResearch.WordTrace tailWord_2888415 prefixEnd_2888415 988763483104281197819285 := by
  unfold tailWord_2888415
  simp only [CollatzResearch.WordTrace]
  refine ⟨105349149830773231853330699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70232766553848821235553799 105349149830773231853330699)
  ·
    refine ⟨158023724746159847779996049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105349149830773231853330699 158023724746159847779996049)
    ·
      refine ⟨118517793559619885834997037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158023724746159847779996049 118517793559619885834997037)
      ·
        refine ⟨44444172584857457188123889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118517793559619885834997037 44444172584857457188123889)
        ·
          refine ⟨33333129438643092891092917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44444172584857457188123889 33333129438643092891092917)
          ·
            refine ⟨3124980884872789958539961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33333129438643092891092917 3124980884872789958539961)
            ·
              refine ⟨2343735663654592468904971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3124980884872789958539961 2343735663654592468904971)
              ·
                refine ⟨3515603495481888703357457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2343735663654592468904971 3515603495481888703357457)
                ·
                  refine ⟨2636702621611416527518093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3515603495481888703357457 2636702621611416527518093)
                  ·
                    refine ⟨988763483104281197819285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2636702621611416527518093 988763483104281197819285)
                    ·
                      rfl

theorem cell22_2888415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 2, 3].length) (baseStart_2888415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888415 prefixEnd_2888415 := by exact prefixLift 2888415
  have htrace : WordTrace (prefixWord ++ tailWord_2888415) baseStart_2888415 baseEnd_2888415 := by
    simpa [prefixWord, tailWord_2888415, baseEnd_2888415] using wordTrace_append hprefix tailTrace_2888415
  have hstable : (prefixWord ++ tailWord_2888415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888415).length < 2 ^ (prefixWord ++ tailWord_2888415).sum := by decide
  have hdescent : baseEnd_2888415 < baseStart_2888415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888426 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 5, 3]
def baseStart_2888426 : Nat := 118140960795 + 2888426 * 2 ^ 59
def prefixEnd_2888426 : Nat := 4983230072969 + 3 ^ 40 * 2888426 * 2
def baseEnd_2888426 : Nat := 988767248629080835794251

theorem tailTrace_2888426 : CollatzResearch.WordTrace tailWord_2888426 prefixEnd_2888426 988767248629080835794251 := by
  unfold tailWord_2888426
  simp only [CollatzResearch.WordTrace]
  refine ⟨26337387758433345182995283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70233034022488920487987421 26337387758433345182995283)
  ·
    refine ⟨39506081637650017774492925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26337387758433345182995283 39506081637650017774492925)
    ·
      refine ⟨14814780614118756665434847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39506081637650017774492925 14814780614118756665434847)
      ·
        refine ⟨22222170921178134998152271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14814780614118756665434847 22222170921178134998152271)
        ·
          refine ⟨33333256381767202497228407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22222170921178134998152271 33333256381767202497228407)
          ·
            refine ⟨49999884572650803745842611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33333256381767202497228407 49999884572650803745842611)
            ·
              refine ⟨74999826858976205618763917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49999884572650803745842611 74999826858976205618763917)
              ·
                refine ⟨28124935072116077107036469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74999826858976205618763917 28124935072116077107036469)
                ·
                  refine ⟨2636712663010882228784669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28124935072116077107036469 2636712663010882228784669)
                  ·
                    refine ⟨988767248629080835794251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2636712663010882228784669 988767248629080835794251)
                    ·
                      rfl

theorem cell22_2888426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_2888426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888426 prefixEnd_2888426 := by exact prefixLift 2888426
  have htrace : WordTrace (prefixWord ++ tailWord_2888426) baseStart_2888426 baseEnd_2888426 := by
    simpa [prefixWord, tailWord_2888426, baseEnd_2888426] using wordTrace_append hprefix tailTrace_2888426
  have hstable : (prefixWord ++ tailWord_2888426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888426).length < 2 ^ (prefixWord ++ tailWord_2888426).sum := by decide
  have hdescent : baseEnd_2888426 < baseStart_2888426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888456 : List Nat := [2, 1, 3, 2, 2, 2, 1, 4, 5]
def baseStart_2888456 : Nat := 118140960795 + 2888456 * 2 ^ 59
def prefixEnd_2888456 : Nat := 4983230072969 + 3 ^ 40 * 2888456 * 2
def baseEnd_2888456 : Nat := 329592506080723585848053

theorem tailTrace_2888456 : CollatzResearch.WordTrace tailWord_2888456 prefixEnd_2888456 329592506080723585848053 := by
  unfold tailWord_2888456
  simp only [CollatzResearch.WordTrace]
  refine ⟨52675322611812347927786611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70233763482416463903715481 52675322611812347927786611)
  ·
    refine ⟨79012983917718521891679917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52675322611812347927786611 79012983917718521891679917)
    ·
      refine ⟨29629868969144445709379969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79012983917718521891679917 29629868969144445709379969)
      ·
        refine ⟨22222401726858334282034977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29629868969144445709379969 22222401726858334282034977)
        ·
          refine ⟨16666801295143750711526233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22222401726858334282034977 16666801295143750711526233)
          ·
            refine ⟨12500100971357813033644675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16666801295143750711526233 12500100971357813033644675)
            ·
              refine ⟨18750151457036719550467013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12500100971357813033644675 18750151457036719550467013)
              ·
                refine ⟨3515653398194384915712565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18750151457036719550467013 3515653398194384915712565)
                ·
                  refine ⟨329592506080723585848053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3515653398194384915712565 329592506080723585848053)
                  ·
                    rfl

theorem cell22_2888456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 4, 5].length) (baseStart_2888456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888456 prefixEnd_2888456 := by exact prefixLift 2888456
  have htrace : WordTrace (prefixWord ++ tailWord_2888456) baseStart_2888456 baseEnd_2888456 := by
    simpa [prefixWord, tailWord_2888456, baseEnd_2888456] using wordTrace_append hprefix tailTrace_2888456
  have hstable : (prefixWord ++ tailWord_2888456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888456).length < 2 ^ (prefixWord ++ tailWord_2888456).sum := by decide
  have hdescent : baseEnd_2888456 < baseStart_2888456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888625 : List Nat := [1, 2, 2, 4, 3, 1, 2, 2, 5]
def baseStart_2888625 : Nat := 118140960795 + 2888625 * 2 ^ 59
def prefixEnd_2888625 : Nat := 4983230072969 + 3 ^ 40 * 2888625 * 2
def baseEnd_2888625 : Nat := 329611790131970216689547

theorem tailTrace_2888625 : CollatzResearch.WordTrace tailWord_2888625 prefixEnd_2888625 329611790131970216689547 := by
  unfold tailWord_2888625
  simp only [CollatzResearch.WordTrace]
  refine ⟨105356809160012437718475329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70237872773341625145650219 105356809160012437718475329)
  ·
    refine ⟨79017606870009328288856497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105356809160012437718475329 79017606870009328288856497)
    ·
      refine ⟨59263205152506996216642373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79017606870009328288856497 59263205152506996216642373)
      ·
        refine ⟨11111850966095061790620445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59263205152506996216642373 11111850966095061790620445)
        ·
          refine ⟨4166944112285648171482667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11111850966095061790620445 4166944112285648171482667)
          ·
            refine ⟨6250416168428472257224001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4166944112285648171482667 6250416168428472257224001)
            ·
              refine ⟨4687812126321354192918001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6250416168428472257224001 4687812126321354192918001)
              ·
                refine ⟨3515859094741015644688501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687812126321354192918001 3515859094741015644688501)
                ·
                  refine ⟨329611790131970216689547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3515859094741015644688501 329611790131970216689547)
                  ·
                    rfl

theorem cell22_2888625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 2, 5].length) (baseStart_2888625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888625 prefixEnd_2888625 := by exact prefixLift 2888625
  have htrace : WordTrace (prefixWord ++ tailWord_2888625) baseStart_2888625 baseEnd_2888625 := by
    simpa [prefixWord, tailWord_2888625, baseEnd_2888625] using wordTrace_append hprefix tailTrace_2888625
  have hstable : (prefixWord ++ tailWord_2888625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888625).length < 2 ^ (prefixWord ++ tailWord_2888625).sum := by decide
  have hdescent : baseEnd_2888625 < baseStart_2888625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888638 : List Nat := [4, 2, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2888638 : Nat := 118140960795 + 2888638 * 2 ^ 59
def prefixEnd_2888638 : Nat := 4983230072969 + 3 ^ 40 * 2888638 * 2
def baseEnd_2888638 : Nat := 988839820561582949493601

theorem tailTrace_2888638 : CollatzResearch.WordTrace tailWord_2888638 prefixEnd_2888638 988839820561582949493601 := by
  unfold tailWord_2888638
  simp only [CollatzResearch.WordTrace]
  refine ⟨13169660413620667617337321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70238188872643560625799045 13169660413620667617337321)
  ·
    refine ⟨9877245310215500713002991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13169660413620667617337321 9877245310215500713002991)
    ·
      refine ⟨14815867965323251069504487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9877245310215500713002991 14815867965323251069504487)
      ·
        refine ⟨22223801947984876604256731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14815867965323251069504487 22223801947984876604256731)
        ·
          refine ⟨33335702921977314906385097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22223801947984876604256731 33335702921977314906385097)
          ·
            refine ⟨25001777191482986179788823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33335702921977314906385097 25001777191482986179788823)
            ·
              refine ⟨37502665787224479269683235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25001777191482986179788823 37502665787224479269683235)
              ·
                refine ⟨56253998680836718904524853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37502665787224479269683235 56253998680836718904524853)
                ·
                  refine ⟨5273812376328442397299205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56253998680836718904524853 5273812376328442397299205)
                  ·
                    refine ⟨988839820561582949493601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5273812376328442397299205 988839820561582949493601)
                    ·
                      rfl

theorem cell22_2888638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2888638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888638 prefixEnd_2888638 := by exact prefixLift 2888638
  have htrace : WordTrace (prefixWord ++ tailWord_2888638) baseStart_2888638 baseEnd_2888638 := by
    simpa [prefixWord, tailWord_2888638, baseEnd_2888638] using wordTrace_append hprefix tailTrace_2888638
  have hstable : (prefixWord ++ tailWord_2888638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888638).length < 2 ^ (prefixWord ++ tailWord_2888638).sum := by decide
  have hdescent : baseEnd_2888638 < baseStart_2888638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888715 : List Nat := [1, 1, 1, 1, 6, 4, 2, 6]
def baseStart_2888715 : Nat := 118140960795 + 2888715 * 2 ^ 59
def prefixEnd_2888715 : Nat := 4983230072969 + 3 ^ 40 * 2888715 * 2
def baseEnd_2888715 : Nat := 109874019915020046146485

theorem tailTrace_2888715 : CollatzResearch.WordTrace tailWord_2888715 prefixEnd_2888715 109874019915020046146485 := by
  unfold tailWord_2888715
  simp only [CollatzResearch.WordTrace]
  refine ⟨105360091729686383089251599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70240061153124255392834399 105360091729686383089251599)
  ·
    refine ⟨158040137594529574633877399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105360091729686383089251599 158040137594529574633877399)
    ·
      refine ⟨237060206391794361950816099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158040137594529574633877399 237060206391794361950816099)
      ·
        refine ⟨355590309587691542926224149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237060206391794361950816099 355590309587691542926224149)
        ·
          refine ⟨16668295761923041074666757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 355590309587691542926224149 16668295761923041074666757)
          ·
            refine ⟨3125305455360570201500017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16668295761923041074666757 3125305455360570201500017)
            ·
              refine ⟨2343979091520427651125013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3125305455360570201500017 2343979091520427651125013)
              ·
                refine ⟨109874019915020046146485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2343979091520427651125013 109874019915020046146485)
                ·
                  rfl

theorem cell22_2888715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 6].length) (baseStart_2888715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888715 prefixEnd_2888715 := by exact prefixLift 2888715
  have htrace : WordTrace (prefixWord ++ tailWord_2888715) baseStart_2888715 baseEnd_2888715 := by
    simpa [prefixWord, tailWord_2888715, baseEnd_2888715] using wordTrace_append hprefix tailTrace_2888715
  have hstable : (prefixWord ++ tailWord_2888715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888715).length < 2 ^ (prefixWord ++ tailWord_2888715).sum := by decide
  have hdescent : baseEnd_2888715 < baseStart_2888715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888760 : List Nat := [2, 1, 2, 1, 5, 2, 1, 3, 5]
def baseStart_2888760 : Nat := 118140960795 + 2888760 * 2 ^ 59
def prefixEnd_2888760 : Nat := 4983230072969 + 3 ^ 40 * 2888760 * 2
def baseEnd_2888760 : Nat := 329627194551605099314409

theorem tailTrace_2888760 : CollatzResearch.WordTrace tailWord_2888760 prefixEnd_2888760 329627194551605099314409 := by
  unfold tailWord_2888760
  simp only [CollatzResearch.WordTrace]
  refine ⟨52680866507261677887319867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70241155343015570516426489 52680866507261677887319867)
  ·
    refine ⟨79021299760892516830979801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52680866507261677887319867 79021299760892516830979801)
    ·
      refine ⟨59265974820669387623234851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79021299760892516830979801 59265974820669387623234851)
      ·
        refine ⟨88898962231004081434852277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59265974820669387623234851 88898962231004081434852277)
        ·
          refine ⟨8334277709156632634517401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88898962231004081434852277 8334277709156632634517401)
          ·
            refine ⟨6250708281867474475888051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8334277709156632634517401 6250708281867474475888051)
            ·
              refine ⟨9376062422801211713832077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6250708281867474475888051 9376062422801211713832077)
              ·
                refine ⟨3516023408550454392687029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9376062422801211713832077 3516023408550454392687029)
                ·
                  refine ⟨329627194551605099314409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3516023408550454392687029 329627194551605099314409)
                  ·
                    rfl

theorem cell22_2888760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 3, 5].length) (baseStart_2888760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888760 prefixEnd_2888760 := by exact prefixLift 2888760
  have htrace : WordTrace (prefixWord ++ tailWord_2888760) baseStart_2888760 baseEnd_2888760 := by
    simpa [prefixWord, tailWord_2888760, baseEnd_2888760] using wordTrace_append hprefix tailTrace_2888760
  have hstable : (prefixWord ++ tailWord_2888760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888760).length < 2 ^ (prefixWord ++ tailWord_2888760).sum := by decide
  have hdescent : baseEnd_2888760 < baseStart_2888760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888798 : List Nat := [4, 4, 1, 1, 1, 2, 1, 4, 1, 3]
def baseStart_2888798 : Nat := 118140960795 + 2888798 * 2 ^ 59
def prefixEnd_2888798 : Nat := 4983230072969 + 3 ^ 40 * 2888798 * 2
def baseEnd_2888798 : Nat := 988894591831395865493111

theorem tailTrace_2888798 : CollatzResearch.WordTrace tailWord_2888798 prefixEnd_2888798 988894591831395865493111 := by
  unfold tailWord_2888798
  simp only [CollatzResearch.WordTrace]
  refine ⟨13170389873548211033065381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70242079325590458843015365 13170389873548211033065381)
  ·
    refine ⟨2469448101290289568699759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13170389873548211033065381 2469448101290289568699759)
    ·
      refine ⟨3704172151935434353049639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469448101290289568699759 3704172151935434353049639)
      ·
        refine ⟨5556258227903151529574459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3704172151935434353049639 5556258227903151529574459)
        ·
          refine ⟨8334387341854727294361689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5556258227903151529574459 8334387341854727294361689)
          ·
            refine ⟨6250790506391045470771267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8334387341854727294361689 6250790506391045470771267)
            ·
              refine ⟨9376185759586568206156901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6250790506391045470771267 9376185759586568206156901)
              ·
                refine ⟨1758034829922481538654419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9376185759586568206156901 1758034829922481538654419)
                ·
                  refine ⟨2637052244883722307981629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758034829922481538654419 2637052244883722307981629)
                  ·
                    refine ⟨988894591831395865493111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2637052244883722307981629 988894591831395865493111)
                    ·
                      rfl

theorem cell22_2888798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_2888798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888798 prefixEnd_2888798 := by exact prefixLift 2888798
  have htrace : WordTrace (prefixWord ++ tailWord_2888798) baseStart_2888798 baseEnd_2888798 := by
    simpa [prefixWord, tailWord_2888798, baseEnd_2888798] using wordTrace_append hprefix tailTrace_2888798
  have hstable : (prefixWord ++ tailWord_2888798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888798).length < 2 ^ (prefixWord ++ tailWord_2888798).sum := by decide
  have hdescent : baseEnd_2888798 < baseStart_2888798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888803 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 5, 5]
def baseStart_2888803 : Nat := 118140960795 + 2888803 * 2 ^ 59
def prefixEnd_2888803 : Nat := 4983230072969 + 3 ^ 40 * 2888803 * 2
def baseEnd_2888803 : Nat := 988896303433577519118095

theorem tailTrace_2888803 : CollatzResearch.WordTrace tailWord_2888803 prefixEnd_2888803 988896303433577519118095 := by
  unfold tailWord_2888803
  simp only [CollatzResearch.WordTrace]
  refine ⟨105363301353367574118455063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70242200902245049412303375 105363301353367574118455063)
  ·
    refine ⟨158044952030051361177682595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105363301353367574118455063 158044952030051361177682595)
    ·
      refine ⟨237067428045077041766523893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158044952030051361177682595 237067428045077041766523893)
      ·
        refine ⟨22225071379225972665611615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 237067428045077041766523893 22225071379225972665611615)
        ·
          refine ⟨33337607068838958998417423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22225071379225972665611615 33337607068838958998417423)
          ·
            refine ⟨50006410603258438497626135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33337607068838958998417423 50006410603258438497626135)
            ·
              refine ⟨75009615904887657746439203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50006410603258438497626135 75009615904887657746439203)
              ·
                refine ⟨112514423857331486619658805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75009615904887657746439203 112514423857331486619658805)
                ·
                  refine ⟨10548227236624826870593013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 112514423857331486619658805 10548227236624826870593013)
                  ·
                    refine ⟨988896303433577519118095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10548227236624826870593013 988896303433577519118095)
                    ·
                      rfl

theorem cell22_2888803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 5].length) (baseStart_2888803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888803 prefixEnd_2888803 := by exact prefixLift 2888803
  have htrace : WordTrace (prefixWord ++ tailWord_2888803) baseStart_2888803 baseEnd_2888803 := by
    simpa [prefixWord, tailWord_2888803, baseEnd_2888803] using wordTrace_append hprefix tailTrace_2888803
  have hstable : (prefixWord ++ tailWord_2888803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888803).length < 2 ^ (prefixWord ++ tailWord_2888803).sum := by decide
  have hdescent : baseEnd_2888803 < baseStart_2888803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888850 : List Nat := [3, 2, 3, 1, 1, 3, 9]
def baseStart_2888850 : Nat := 118140960795 + 2888850 * 2 ^ 59
def prefixEnd_2888850 : Nat := 4983230072969 + 3 ^ 40 * 2888850 * 2
def baseEnd_2888850 : Nat := 36626384907188335673813

theorem tailTrace_2888850 : CollatzResearch.WordTrace tailWord_2888850 prefixEnd_2888850 36626384907188335673813 := by
  unfold tailWord_2888850
  simp only [CollatzResearch.WordTrace]
  refine ⟨26341253896049325286354001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70243343722798200763610669 26341253896049325286354001)
  ·
    refine ⟨19755940422036993964765501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26341253896049325286354001 19755940422036993964765501)
    ·
      refine ⟨7408477658263872736787063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19755940422036993964765501 7408477658263872736787063)
      ·
        refine ⟨11112716487395809105180595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7408477658263872736787063 11112716487395809105180595)
        ·
          refine ⟨16669074731093713657770893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11112716487395809105180595 16669074731093713657770893)
          ·
            refine ⟨6250903024160142621664085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16669074731093713657770893 6250903024160142621664085)
            ·
              refine ⟨36626384907188335673813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6250903024160142621664085 36626384907188335673813)
              ·
                rfl

theorem cell22_2888850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 9].length) (baseStart_2888850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888850 prefixEnd_2888850 := by exact prefixLift 2888850
  have htrace : WordTrace (prefixWord ++ tailWord_2888850) baseStart_2888850 baseEnd_2888850 := by
    simpa [prefixWord, tailWord_2888850, baseEnd_2888850] using wordTrace_append hprefix tailTrace_2888850
  have hstable : (prefixWord ++ tailWord_2888850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888850).length < 2 ^ (prefixWord ++ tailWord_2888850).sum := by decide
  have hdescent : baseEnd_2888850 < baseStart_2888850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888871 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 2, 3]
def baseStart_2888871 : Nat := 118140960795 + 2888871 * 2 ^ 59
def prefixEnd_2888871 : Nat := 4983230072969 + 3 ^ 40 * 2888871 * 2
def baseEnd_2888871 : Nat := 988919581223248008417887

theorem tailTrace_2888871 : CollatzResearch.WordTrace tailWord_2888871 prefixEnd_2888871 988919581223248008417887 := by
  unfold tailWord_2888871
  simp only [CollatzResearch.WordTrace]
  refine ⟨105365781517121221731930467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70243854344747481154620311 105365781517121221731930467)
  ·
    refine ⟨158048672275681832597895701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105365781517121221731930467 158048672275681832597895701)
    ·
      refine ⟨7408531512922585903026361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 158048672275681832597895701 7408531512922585903026361)
      ·
        refine ⟨5556398634691939427269771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7408531512922585903026361 5556398634691939427269771)
        ·
          refine ⟨8334597952037909140904657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5556398634691939427269771 8334597952037909140904657)
          ·
            refine ⟨6250948464028431855678493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8334597952037909140904657 6250948464028431855678493)
            ·
              refine ⟨2344105674010661945879435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6250948464028431855678493 2344105674010661945879435)
              ·
                refine ⟨3516158511015992918819153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344105674010661945879435 3516158511015992918819153)
                ·
                  refine ⟨2637118883261994689114365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3516158511015992918819153 2637118883261994689114365)
                  ·
                    refine ⟨988919581223248008417887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2637118883261994689114365 988919581223248008417887)
                    ·
                      rfl

theorem cell22_2888871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_2888871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888871 prefixEnd_2888871 := by exact prefixLift 2888871
  have htrace : WordTrace (prefixWord ++ tailWord_2888871) baseStart_2888871 baseEnd_2888871 := by
    simpa [prefixWord, tailWord_2888871, baseEnd_2888871] using wordTrace_append hprefix tailTrace_2888871
  have hstable : (prefixWord ++ tailWord_2888871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888871).length < 2 ^ (prefixWord ++ tailWord_2888871).sum := by decide
  have hdescent : baseEnd_2888871 < baseStart_2888871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888882 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 3, 3]
def baseStart_2888882 : Nat := 118140960795 + 2888882 * 2 ^ 59
def prefixEnd_2888882 : Nat := 4983230072969 + 3 ^ 40 * 2888882 * 2
def baseEnd_2888882 : Nat := 988923346748047646392853

theorem tailTrace_2888882 : CollatzResearch.WordTrace tailWord_2888882 prefixEnd_2888882 988923346748047646392853 := by
  unfold tailWord_2888882
  simp only [CollatzResearch.WordTrace]
  refine ⟨26341545680020342652645225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70244121813387580407053933 26341545680020342652645225)
  ·
    refine ⟨19756159260015256989483919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26341545680020342652645225 19756159260015256989483919)
    ·
      refine ⟨29634238890022885484225879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19756159260015256989483919 29634238890022885484225879)
      ·
        refine ⟨44451358335034328226338819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29634238890022885484225879 44451358335034328226338819)
        ·
          refine ⟨66677037502551492339508229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44451358335034328226338819 66677037502551492339508229)
          ·
            refine ⟨12501944531728404813657793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66677037502551492339508229 12501944531728404813657793)
            ·
              refine ⟨9376458398796303610243345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12501944531728404813657793 9376458398796303610243345)
              ·
                refine ⟨7032343799097227707682509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9376458398796303610243345 7032343799097227707682509)
                ·
                  refine ⟨2637128924661460390380941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7032343799097227707682509 2637128924661460390380941)
                  ·
                    refine ⟨988923346748047646392853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2637128924661460390380941 988923346748047646392853)
                    ·
                      rfl

theorem cell22_2888882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 3, 3].length) (baseStart_2888882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888882 prefixEnd_2888882 := by exact prefixLift 2888882
  have htrace : WordTrace (prefixWord ++ tailWord_2888882) baseStart_2888882 baseEnd_2888882 := by
    simpa [prefixWord, tailWord_2888882, baseEnd_2888882] using wordTrace_append hprefix tailTrace_2888882
  have hstable : (prefixWord ++ tailWord_2888882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888882).length < 2 ^ (prefixWord ++ tailWord_2888882).sum := by decide
  have hdescent : baseEnd_2888882 < baseStart_2888882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888929 : List Nat := [1, 2, 3, 1, 3, 4, 2, 1, 5]
def baseStart_2888929 : Nat := 118140960795 + 2888929 * 2 ^ 59
def prefixEnd_2888929 : Nat := 4983230072969 + 3 ^ 40 * 2888929 * 2
def baseEnd_2888929 : Nat := 329646478602851730155903

theorem tailTrace_2888929 : CollatzResearch.WordTrace tailWord_2888929 prefixEnd_2888929 329646478602851730155903 := by
  unfold tailWord_2888929
  simp only [CollatzResearch.WordTrace]
  refine ⟨105367896950911097637541841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70245264633940731758361227 105367896950911097637541841)
  ·
    refine ⟨79025922713183323228156381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105367896950911097637541841 79025922713183323228156381)
    ·
      refine ⟨29634721017443746210558643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79025922713183323228156381 29634721017443746210558643)
      ·
        refine ⟨44452081526165619315837965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29634721017443746210558643 44452081526165619315837965)
        ·
          refine ⟨16669530572312107243439237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44452081526165619315837965 16669530572312107243439237)
          ·
            refine ⟨3125536982308520108144857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16669530572312107243439237 3125536982308520108144857)
            ·
              refine ⟨2344152736731390081108643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3125536982308520108144857 2344152736731390081108643)
              ·
                refine ⟨3516229105097085121662965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344152736731390081108643 3516229105097085121662965)
                ·
                  refine ⟨329646478602851730155903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3516229105097085121662965 329646478602851730155903)
                  ·
                    rfl

theorem cell22_2888929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2, 1, 5].length) (baseStart_2888929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888929 prefixEnd_2888929 := by exact prefixLift 2888929
  have htrace : WordTrace (prefixWord ++ tailWord_2888929) baseStart_2888929 baseEnd_2888929 := by
    simpa [prefixWord, tailWord_2888929, baseEnd_2888929] using wordTrace_append hprefix tailTrace_2888929
  have hstable : (prefixWord ++ tailWord_2888929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888929).length < 2 ^ (prefixWord ++ tailWord_2888929).sum := by decide
  have hdescent : baseEnd_2888929 < baseStart_2888929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888959 : List Nat := [1, 1, 2, 2, 1, 6, 3, 1, 1, 4]
def baseStart_2888959 : Nat := 118140960795 + 2888959 * 2 ^ 59
def prefixEnd_2888959 : Nat := 4983230072969 + 3 ^ 40 * 2888959 * 2
def baseEnd_2888959 : Nat := 988949705421645112217617

theorem tailTrace_2888959 : CollatzResearch.WordTrace tailWord_2888959 prefixEnd_2888959 988949705421645112217617 := by
  unfold tailWord_2888959
  simp only [CollatzResearch.WordTrace]
  refine ⟨105368991140802412761133931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70245994093868275174089287 105368991140802412761133931)
  ·
    refine ⟨158053486711203619141700897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105368991140802412761133931 158053486711203619141700897)
    ·
      refine ⟨118540115033402714356275673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158053486711203619141700897 118540115033402714356275673)
      ·
        refine ⟨88905086275052035767206755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118540115033402714356275673 88905086275052035767206755)
        ·
          refine ⟨133357629412578053650810133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88905086275052035767206755 133357629412578053650810133)
          ·
            refine ⟨6251138878714596264881725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133357629412578053650810133 6251138878714596264881725)
            ·
              refine ⟨2344177079517973599330647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6251138878714596264881725 2344177079517973599330647)
              ·
                refine ⟨3516265619276960398995971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2344177079517973599330647 3516265619276960398995971)
                ·
                  refine ⟨5274398428915440598493957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3516265619276960398995971 5274398428915440598493957)
                  ·
                    refine ⟨988949705421645112217617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5274398428915440598493957 988949705421645112217617)
                    ·
                      rfl

theorem cell22_2888959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 1, 4].length) (baseStart_2888959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888959 prefixEnd_2888959 := by exact prefixLift 2888959
  have htrace : WordTrace (prefixWord ++ tailWord_2888959) baseStart_2888959 baseEnd_2888959 := by
    simpa [prefixWord, tailWord_2888959, baseEnd_2888959] using wordTrace_append hprefix tailTrace_2888959
  have hstable : (prefixWord ++ tailWord_2888959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888959).length < 2 ^ (prefixWord ++ tailWord_2888959).sum := by decide
  have hdescent : baseEnd_2888959 < baseStart_2888959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888970 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 3, 6]
def baseStart_2888970 : Nat := 118140960795 + 2888970 * 2 ^ 59
def prefixEnd_2888970 : Nat := 4983230072969 + 3 ^ 40 * 2888970 * 2
def baseEnd_2888970 : Nat := 988953470946444750192583

theorem tailTrace_2888970 : CollatzResearch.WordTrace tailWord_2888970 prefixEnd_2888970 988953470946444750192583 := by
  unfold tailWord_2888970
  simp only [CollatzResearch.WordTrace]
  refine ⟨26342348085940640409946091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70246261562508374426522909 26342348085940640409946091)
  ·
    refine ⟨39513522128910960614919137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26342348085940640409946091 39513522128910960614919137)
    ·
      refine ⟨29635141596683220461189353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39513522128910960614919137 29635141596683220461189353)
      ·
        refine ⟨22226356197512415345892015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29635141596683220461189353 22226356197512415345892015)
        ·
          refine ⟨33339534296268623018838023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22226356197512415345892015 33339534296268623018838023)
          ·
            refine ⟨50009301444402934528257035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33339534296268623018838023 50009301444402934528257035)
            ·
              refine ⟨75013952166604401792385553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50009301444402934528257035 75013952166604401792385553)
              ·
                refine ⟨56260464124953301344289165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75013952166604401792385553 56260464124953301344289165)
                ·
                  refine ⟨21097674046857488004108437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56260464124953301344289165 21097674046857488004108437)
                  ·
                    refine ⟨988953470946444750192583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21097674046857488004108437 988953470946444750192583)
                    ·
                      rfl

theorem cell22_2888970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 3, 6].length) (baseStart_2888970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888970 prefixEnd_2888970 := by exact prefixLift 2888970
  have htrace : WordTrace (prefixWord ++ tailWord_2888970) baseStart_2888970 baseEnd_2888970 := by
    simpa [prefixWord, tailWord_2888970, baseEnd_2888970] using wordTrace_append hprefix tailTrace_2888970
  have hstable : (prefixWord ++ tailWord_2888970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888970).length < 2 ^ (prefixWord ++ tailWord_2888970).sum := by decide
  have hdescent : baseEnd_2888970 < baseStart_2888970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888974 : List Nat := [4, 1, 1, 2, 1, 4, 1, 4, 4]
def baseStart_2888974 : Nat := 118140960795 + 2888974 * 2 ^ 59
def prefixEnd_2888974 : Nat := 4983230072969 + 3 ^ 40 * 2888974 * 2
def baseEnd_2888974 : Nat := 329651613409396691030857

theorem tailTrace_2888974 : CollatzResearch.WordTrace tailWord_2888974 prefixEnd_2888974 329651613409396691030857 := by
  unfold tailWord_2888974
  simp only [CollatzResearch.WordTrace]
  refine ⟨13171192279468508790366247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70246358823832046881953317 13171192279468508790366247)
  ·
    refine ⟨19756788419202763185549371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13171192279468508790366247 19756788419202763185549371)
    ·
      refine ⟨29635182628804144778324057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19756788419202763185549371 29635182628804144778324057)
      ·
        refine ⟨22226386971603108583743043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29635182628804144778324057 22226386971603108583743043)
        ·
          refine ⟨33339580457404662875614565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22226386971603108583743043 33339580457404662875614565)
          ·
            refine ⟨6251171335763374289177731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33339580457404662875614565 6251171335763374289177731)
            ·
              refine ⟨9376757003645061433766597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6251171335763374289177731 9376757003645061433766597)
              ·
                refine ⟨1758141938183449018831237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9376757003645061433766597 1758141938183449018831237)
                ·
                  refine ⟨329651613409396691030857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1758141938183449018831237 329651613409396691030857)
                  ·
                    rfl

theorem cell22_2888974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_2888974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888974 prefixEnd_2888974 := by exact prefixLift 2888974
  have htrace : WordTrace (prefixWord ++ tailWord_2888974) baseStart_2888974 baseEnd_2888974 := by
    simpa [prefixWord, tailWord_2888974, baseEnd_2888974] using wordTrace_append hprefix tailTrace_2888974
  have hstable : (prefixWord ++ tailWord_2888974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888974).length < 2 ^ (prefixWord ++ tailWord_2888974).sum := by decide
  have hdescent : baseEnd_2888974 < baseStart_2888974 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2888989 : List Nat := [1, 4, 2, 3, 1, 2, 2, 1, 1, 5]
def baseStart_2888989 : Nat := 118140960795 + 2888989 * 2 ^ 59
def prefixEnd_2888989 : Nat := 4983230072969 + 3 ^ 40 * 2888989 * 2
def baseEnd_2888989 : Nat := 988959975034735033967525

theorem tailTrace_2888989 : CollatzResearch.WordTrace tailWord_2888989 prefixEnd_2888989 988959975034735033967525 := by
  unfold tailWord_2888989
  simp only [CollatzResearch.WordTrace]
  refine ⟨105370085330693727884726021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70246723553795818589817347 105370085330693727884726021)
  ·
    refine ⟨19756890999505073978386129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105370085330693727884726021 19756890999505073978386129)
    ·
      refine ⟨14817668249628805483789597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19756890999505073978386129 14817668249628805483789597)
      ·
        refine ⟨5556625593610802056421099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14817668249628805483789597 5556625593610802056421099)
        ·
          refine ⟨8334938390416203084631649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5556625593610802056421099 8334938390416203084631649)
          ·
            refine ⟨6251203792812152313473737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8334938390416203084631649 6251203792812152313473737)
            ·
              refine ⟨4688402844609114235105303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6251203792812152313473737 4688402844609114235105303)
              ·
                refine ⟨7032604266913671352657955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4688402844609114235105303 7032604266913671352657955)
                ·
                  refine ⟨10548906400370507028986933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7032604266913671352657955 10548906400370507028986933)
                  ·
                    refine ⟨988959975034735033967525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10548906400370507028986933 988959975034735033967525)
                    ·
                      rfl

theorem cell22_2888989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_2888989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2888989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2888989 prefixEnd_2888989 := by exact prefixLift 2888989
  have htrace : WordTrace (prefixWord ++ tailWord_2888989) baseStart_2888989 baseEnd_2888989 := by
    simpa [prefixWord, tailWord_2888989, baseEnd_2888989] using wordTrace_append hprefix tailTrace_2888989
  have hstable : (prefixWord ++ tailWord_2888989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2888989).length < 2 ^ (prefixWord ++ tailWord_2888989).sum := by decide
  have hdescent : baseEnd_2888989 < baseStart_2888989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2888989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889068 : List Nat := [2, 2, 1, 1, 5, 3, 1, 3, 1, 3]
def baseStart_2889068 : Nat := 118140960795 + 2889068 * 2 ^ 59
def prefixEnd_2889068 : Nat := 4983230072969 + 3 ^ 40 * 2889068 * 2
def baseEnd_2889068 : Nat := 988987018349205161242283

theorem tailTrace_2889068 : CollatzResearch.WordTrace tailWord_2889068 prefixEnd_2889068 988987018349205161242283 := by
  unfold tailWord_2889068
  simp only [CollatzResearch.WordTrace]
  refine ⟨52686483348703762188425929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70248644464938349584567905 52686483348703762188425929)
  ·
    refine ⟨39514862511527821641319447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52686483348703762188425929 39514862511527821641319447)
    ·
      refine ⟨59272293767291732461979171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39514862511527821641319447 59272293767291732461979171)
      ·
        refine ⟨88908440650937598692968757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59272293767291732461979171 88908440650937598692968757)
        ·
          refine ⟨8335166311025399877465821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 88908440650937598692968757 8335166311025399877465821)
          ·
            refine ⟨3125687366634524954049683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8335166311025399877465821 3125687366634524954049683)
            ·
              refine ⟨4688531049951787431074525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3125687366634524954049683 4688531049951787431074525)
              ·
                refine ⟨1758199143731920286652947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4688531049951787431074525 1758199143731920286652947)
                ·
                  refine ⟨2637298715597880429979421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758199143731920286652947 2637298715597880429979421)
                  ·
                    refine ⟨988987018349205161242283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2637298715597880429979421 988987018349205161242283)
                    ·
                      rfl

theorem cell22_2889068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 1, 3].length) (baseStart_2889068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889068 prefixEnd_2889068 := by exact prefixLift 2889068
  have htrace : WordTrace (prefixWord ++ tailWord_2889068) baseStart_2889068 baseEnd_2889068 := by
    simpa [prefixWord, tailWord_2889068, baseEnd_2889068] using wordTrace_append hprefix tailTrace_2889068
  have hstable : (prefixWord ++ tailWord_2889068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889068).length < 2 ^ (prefixWord ++ tailWord_2889068).sum := by decide
  have hdescent : baseEnd_2889068 < baseStart_2889068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889141 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 2, 3]
def baseStart_2889141 : Nat := 118140960795 + 2889141 * 2 ^ 59
def prefixEnd_2889141 : Nat := 4983230072969 + 3 ^ 40 * 2889141 * 2
def baseEnd_2889141 : Nat := 989012007741057304167059

theorem tailTrace_2889141 : CollatzResearch.WordTrace tailWord_2889141 prefixEnd_2889141 989012007741057304167059 := by
  unfold tailWord_2889141
  simp only [CollatzResearch.WordTrace]
  refine ⟨105375629226143057844259277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70250419484095371896172851 105375629226143057844259277)
  ·
    refine ⟨39515860959803646691597229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105375629226143057844259277 39515860959803646691597229)
    ·
      refine ⟨14818447859926367509348961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39515860959803646691597229 14818447859926367509348961)
      ·
        refine ⟨11113835894944775632011721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14818447859926367509348961 11113835894944775632011721)
        ·
          refine ⟨8335376921208581724008791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11113835894944775632011721 8335376921208581724008791)
          ·
            refine ⟨12503065381812872586013187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8335376921208581724008791 12503065381812872586013187)
            ·
              refine ⟨18754598072719308879019781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12503065381812872586013187 18754598072719308879019781)
              ·
                refine ⟨3516487138634870414816209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18754598072719308879019781 3516487138634870414816209)
                ·
                  refine ⟨2637365353976152811112157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3516487138634870414816209 2637365353976152811112157)
                  ·
                    refine ⟨989012007741057304167059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2637365353976152811112157 989012007741057304167059)
                    ·
                      rfl

theorem cell22_2889141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_2889141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889141 prefixEnd_2889141 := by exact prefixLift 2889141
  have htrace : WordTrace (prefixWord ++ tailWord_2889141) baseStart_2889141 baseEnd_2889141 := by
    simpa [prefixWord, tailWord_2889141, baseEnd_2889141] using wordTrace_append hprefix tailTrace_2889141
  have hstable : (prefixWord ++ tailWord_2889141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889141).length < 2 ^ (prefixWord ++ tailWord_2889141).sum := by decide
  have hdescent : baseEnd_2889141 < baseStart_2889141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889199 : List Nat := [1, 1, 2, 1, 4, 1, 5, 2, 5]
def baseStart_2889199 : Nat := 118140960795 + 2889199 * 2 ^ 59
def prefixEnd_2889199 : Nat := 4983230072969 + 3 ^ 40 * 2889199 * 2
def baseEnd_2889199 : Nat := 329677287442121495405627

theorem tailTrace_2889199 : CollatzResearch.WordTrace tailWord_2889199 prefixEnd_2889199 329677287442121495405627 := by
  unfold tailWord_2889199
  simp only [CollatzResearch.WordTrace]
  refine ⟨105377744659932933749870651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70251829773288622499913767 105377744659932933749870651)
  ·
    refine ⟨158066616989899400624805977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105377744659932933749870651 158066616989899400624805977)
    ·
      refine ⟨118549962742424550468604483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158066616989899400624805977 118549962742424550468604483)
      ·
        refine ⟨177824944113636825702906725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118549962742424550468604483 177824944113636825702906725)
        ·
          refine ⟨33342177021306904819295011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177824944113636825702906725 33342177021306904819295011)
          ·
            refine ⟨50013265531960357228942517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33342177021306904819295011 50013265531960357228942517)
            ·
              refine ⟨4688743643621283490213361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50013265531960357228942517 4688743643621283490213361)
              ·
                refine ⟨3516557732715962617660021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4688743643621283490213361 3516557732715962617660021)
                ·
                  refine ⟨329677287442121495405627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3516557732715962617660021 329677287442121495405627)
                  ·
                    rfl

theorem cell22_2889199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 2, 5].length) (baseStart_2889199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889199 prefixEnd_2889199 := by exact prefixLift 2889199
  have htrace : WordTrace (prefixWord ++ tailWord_2889199) baseStart_2889199 baseEnd_2889199 := by
    simpa [prefixWord, tailWord_2889199, baseEnd_2889199] using wordTrace_append hprefix tailTrace_2889199
  have hstable : (prefixWord ++ tailWord_2889199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889199).length < 2 ^ (prefixWord ++ tailWord_2889199).sum := by decide
  have hdescent : baseEnd_2889199 < baseStart_2889199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889222 : List Nat := [6, 2, 1, 1, 2, 2, 2, 6]
def baseStart_2889222 : Nat := 118140960795 + 2889222 * 2 ^ 59
def prefixEnd_2889222 : Nat := 4983230072969 + 3 ^ 40 * 2889222 * 2
def baseEnd_2889222 : Nat := 109893303966266676987979

theorem tailTrace_2889222 : CollatzResearch.WordTrace tailWord_2889222 prefixEnd_2889222 109893303966266676987979 := by
  unfold tailWord_2889222
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293080735589050271186185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70252389025899739118638613 3293080735589050271186185)
  ·
    refine ⟨2469810551691787703389639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3293080735589050271186185 2469810551691787703389639)
    ·
      refine ⟨3704715827537681555084459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2469810551691787703389639 3704715827537681555084459)
      ·
        refine ⟨5557073741306522332626689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3704715827537681555084459 5557073741306522332626689)
        ·
          refine ⟨4167805305979891749470017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5557073741306522332626689 4167805305979891749470017)
          ·
            refine ⟨3125853979484918812102513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4167805305979891749470017 3125853979484918812102513)
            ·
              refine ⟨2344390484613689109076885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3125853979484918812102513 2344390484613689109076885)
              ·
                refine ⟨109893303966266676987979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2344390484613689109076885 109893303966266676987979)
                ·
                  rfl

theorem cell22_2889222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_2889222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889222 prefixEnd_2889222 := by exact prefixLift 2889222
  have htrace : WordTrace (prefixWord ++ tailWord_2889222) baseStart_2889222 baseEnd_2889222 := by
    simpa [prefixWord, tailWord_2889222, baseEnd_2889222] using wordTrace_append hprefix tailTrace_2889222
  have hstable : (prefixWord ++ tailWord_2889222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889222).length < 2 ^ (prefixWord ++ tailWord_2889222).sum := by decide
  have hdescent : baseEnd_2889222 < baseStart_2889222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889257 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 12]
def baseStart_2889257 : Nat := 118140960795 + 2889257 * 2 ^ 59
def prefixEnd_2889257 : Nat := 4983230072969 + 3 ^ 40 * 2889257 * 2
def baseEnd_2889257 : Nat := 989051716911671668266703

theorem tailTrace_2889257 : CollatzResearch.WordTrace tailWord_2889257 prefixEnd_2889257 989051716911671668266703 := by
  unfold tailWord_2889257
  simp only [CollatzResearch.WordTrace]
  refine ⟨105379860093722809655482025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70253240062481873103654683 105379860093722809655482025)
  ·
    refine ⟨79034895070292107241611519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105379860093722809655482025 79034895070292107241611519)
    ·
      refine ⟨118552342605438160862417279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79034895070292107241611519 118552342605438160862417279)
      ·
        refine ⟨177828513908157241293625919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118552342605438160862417279 177828513908157241293625919)
        ·
          refine ⟨266742770862235861940438879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177828513908157241293625919 266742770862235861940438879)
          ·
            refine ⟨400114156293353792910658319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 266742770862235861940438879 400114156293353792910658319)
            ·
              refine ⟨600171234440030689365987479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 400114156293353792910658319 600171234440030689365987479)
              ·
                refine ⟨900256851660046034048981219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 600171234440030689365987479 900256851660046034048981219)
                ·
                  refine ⟨1350385277490069051073471829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 900256851660046034048981219 1350385277490069051073471829)
                  ·
                    refine ⟨989051716911671668266703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 12 1350385277490069051073471829 989051716911671668266703)
                    ·
                      rfl

theorem cell22_2889257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 12].length) (baseStart_2889257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889257 prefixEnd_2889257 := by exact prefixLift 2889257
  have htrace : WordTrace (prefixWord ++ tailWord_2889257) baseStart_2889257 baseEnd_2889257 := by
    simpa [prefixWord, tailWord_2889257, baseEnd_2889257] using wordTrace_append hprefix tailTrace_2889257
  have hstable : (prefixWord ++ tailWord_2889257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889257).length < 2 ^ (prefixWord ++ tailWord_2889257).sum := by decide
  have hdescent : baseEnd_2889257 < baseStart_2889257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889274 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 4, 4]
def baseStart_2889274 : Nat := 118140960795 + 2889274 * 2 ^ 59
def prefixEnd_2889274 : Nat := 4983230072969 + 3 ^ 40 * 2889274 * 2
def baseEnd_2889274 : Nat := 989057536359089290591651

theorem tailTrace_2889274 : CollatzResearch.WordTrace tailWord_2889274 prefixEnd_2889274 989057536359089290591651 := by
  unfold tailWord_2889274
  simp only [CollatzResearch.WordTrace]
  refine ⟨26345120033665305389712719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70253653423107481039233917 26345120033665305389712719)
  ·
    refine ⟨39517680050497958084569079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26345120033665305389712719 39517680050497958084569079)
    ·
      refine ⟨59276520075746937126853619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39517680050497958084569079 59276520075746937126853619)
      ·
        refine ⟨88914780113620405690280429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59276520075746937126853619 88914780113620405690280429)
        ·
          refine ⟨33343042542607652133855161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88914780113620405690280429 33343042542607652133855161)
          ·
            refine ⟨25007281906955739100391371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33343042542607652133855161 25007281906955739100391371)
            ·
              refine ⟨37510922860433608650587057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25007281906955739100391371 37510922860433608650587057)
              ·
                refine ⟨28133192145325206487940293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37510922860433608650587057 28133192145325206487940293)
                ·
                  refine ⟨5274973527248476216488805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28133192145325206487940293 5274973527248476216488805)
                  ·
                    refine ⟨989057536359089290591651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5274973527248476216488805 989057536359089290591651)
                    ·
                      rfl

theorem cell22_2889274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 4, 4].length) (baseStart_2889274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889274 prefixEnd_2889274 := by exact prefixLift 2889274
  have htrace : WordTrace (prefixWord ++ tailWord_2889274) baseStart_2889274 baseEnd_2889274 := by
    simpa [prefixWord, tailWord_2889274, baseEnd_2889274] using wordTrace_append hprefix tailTrace_2889274
  have hstable : (prefixWord ++ tailWord_2889274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889274).length < 2 ^ (prefixWord ++ tailWord_2889274).sum := by decide
  have hdescent : baseEnd_2889274 < baseStart_2889274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889293 : List Nat := [1, 6, 1, 1, 3, 1, 1, 2, 1, 5]
def baseStart_2889293 : Nat := 118140960795 + 2889293 * 2 ^ 59
def prefixEnd_2889293 : Nat := 4983230072969 + 3 ^ 40 * 2889293 * 2
def baseEnd_2889293 : Nat := 989064040447379574366593

theorem tailTrace_2889293 : CollatzResearch.WordTrace tailWord_2889293 prefixEnd_2889293 989064040447379574366593 := by
  unfold tailWord_2889293
  simp only [CollatzResearch.WordTrace]
  refine ⟨105381173121592387803792533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70254115414394925202528355 105381173121592387803792533)
  ·
    refine ⟨4939742490074643178302775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105381173121592387803792533 4939742490074643178302775)
    ·
      refine ⟨7409613735111964767454163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4939742490074643178302775 7409613735111964767454163)
      ·
        refine ⟨11114420602667947151181245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7409613735111964767454163 11114420602667947151181245)
        ·
          refine ⟨4167907726000480181692967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11114420602667947151181245 4167907726000480181692967)
          ·
            refine ⟨6251861589000720272539451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4167907726000480181692967 6251861589000720272539451)
            ·
              refine ⟨9377792383501080408809177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6251861589000720272539451 9377792383501080408809177)
              ·
                refine ⟨7033344287625810306606883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9377792383501080408809177 7033344287625810306606883)
                ·
                  refine ⟨10550016431438715459910325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7033344287625810306606883 10550016431438715459910325)
                  ·
                    refine ⟨989064040447379574366593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10550016431438715459910325 989064040447379574366593)
                    ·
                      rfl

theorem cell22_2889293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 2, 1, 5].length) (baseStart_2889293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889293 prefixEnd_2889293 := by exact prefixLift 2889293
  have htrace : WordTrace (prefixWord ++ tailWord_2889293) baseStart_2889293 baseEnd_2889293 := by
    simpa [prefixWord, tailWord_2889293, baseEnd_2889293] using wordTrace_append hprefix tailTrace_2889293
  have hstable : (prefixWord ++ tailWord_2889293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889293).length < 2 ^ (prefixWord ++ tailWord_2889293).sum := by decide
  have hdescent : baseEnd_2889293 < baseStart_2889293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889319 : List Nat := [1, 1, 5, 1, 1, 1, 3, 1, 2, 6]
def baseStart_2889319 : Nat := 118140960795 + 2889319 * 2 ^ 59
def prefixEnd_2889319 : Nat := 4983230072969 + 3 ^ 40 * 2889319 * 2
def baseEnd_2889319 : Nat := 989072940778724173216513

theorem tailTrace_2889319 : CollatzResearch.WordTrace tailWord_2889319 prefixEnd_2889319 989072940778724173216513 := by
  unfold tailWord_2889319
  simp only [CollatzResearch.WordTrace]
  refine ⟨105382121419498194244239011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70254747612998796162826007 105382121419498194244239011)
  ·
    refine ⟨158073182129247291366358517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105382121419498194244239011 158073182129247291366358517)
    ·
      refine ⟨14819360824616933565596111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158073182129247291366358517 14819360824616933565596111)
      ·
        refine ⟨22229041236925400348394167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14819360824616933565596111 22229041236925400348394167)
        ·
          refine ⟨33343561855388100522591251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22229041236925400348394167 33343561855388100522591251)
          ·
            refine ⟨50015342783082150783886877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33343561855388100522591251 50015342783082150783886877)
            ·
              refine ⟨18755753543655806543957579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50015342783082150783886877 18755753543655806543957579)
              ·
                refine ⟨28133630315483709815936369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18755753543655806543957579 28133630315483709815936369)
                ·
                  refine ⟨21100222736612782361952277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28133630315483709815936369 21100222736612782361952277)
                  ·
                    refine ⟨989072940778724173216513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21100222736612782361952277 989072940778724173216513)
                    ·
                      rfl

theorem cell22_2889319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_2889319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889319 prefixEnd_2889319 := by exact prefixLift 2889319
  have htrace : WordTrace (prefixWord ++ tailWord_2889319) baseStart_2889319 baseEnd_2889319 := by
    simpa [prefixWord, tailWord_2889319, baseEnd_2889319] using wordTrace_append hprefix tailTrace_2889319
  have hstable : (prefixWord ++ tailWord_2889319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889319).length < 2 ^ (prefixWord ++ tailWord_2889319).sum := by decide
  have hdescent : baseEnd_2889319 < baseStart_2889319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889349 : List Nat := [1, 3, 1, 1, 4, 1, 1, 2, 1, 7]
def baseStart_2889349 : Nat := 118140960795 + 2889349 * 2 ^ 59
def prefixEnd_2889349 : Nat := 4983230072969 + 3 ^ 40 * 2889349 * 2
def baseEnd_2889349 : Nat := 989083210391814094966421

theorem tailTrace_2889349 : CollatzResearch.WordTrace tailWord_2889349 prefixEnd_2889349 989083210391814094966421 := by
  unfold tailWord_2889349
  simp only [CollatzResearch.WordTrace]
  refine ⟨105383215609389509367831101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70255477072926339578554067 105383215609389509367831101)
  ·
    refine ⟨39518705853521066012936663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105383215609389509367831101 39518705853521066012936663)
    ·
      refine ⟨59278058780281599019404995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39518705853521066012936663 59278058780281599019404995)
      ·
        refine ⟨88917088170422398529107493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59278058780281599019404995 88917088170422398529107493)
        ·
          refine ⟨16671954031954199724207655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 88917088170422398529107493 16671954031954199724207655)
          ·
            refine ⟨25007931047931299586311483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16671954031954199724207655 25007931047931299586311483)
            ·
              refine ⟨37511896571896949379467225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25007931047931299586311483 37511896571896949379467225)
              ·
                refine ⟨28133922428922712034600419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37511896571896949379467225 28133922428922712034600419)
                ·
                  refine ⟨42200883643384068051900629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28133922428922712034600419 42200883643384068051900629)
                  ·
                    refine ⟨989083210391814094966421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42200883643384068051900629 989083210391814094966421)
                    ·
                      rfl

theorem cell22_2889349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_2889349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889349 prefixEnd_2889349 := by exact prefixLift 2889349
  have htrace : WordTrace (prefixWord ++ tailWord_2889349) baseStart_2889349 baseEnd_2889349 := by
    simpa [prefixWord, tailWord_2889349, baseEnd_2889349] using wordTrace_append hprefix tailTrace_2889349
  have hstable : (prefixWord ++ tailWord_2889349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889349).length < 2 ^ (prefixWord ++ tailWord_2889349).sum := by decide
  have hdescent : baseEnd_2889349 < baseStart_2889349 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889368 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 5]
def baseStart_2889368 : Nat := 118140960795 + 2889368 * 2 ^ 59
def prefixEnd_2889368 : Nat := 4983230072969 + 3 ^ 40 * 2889368 * 2
def baseEnd_2889368 : Nat := 329696571493368126247121

theorem tailTrace_2889368 : CollatzResearch.WordTrace tailWord_2889368 prefixEnd_2889368 329696571493368126247121 := by
  unfold tailWord_2889368
  simp only [CollatzResearch.WordTrace]
  refine ⟨52691954298160337806386379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70255939064213783741848505 52691954298160337806386379)
  ·
    refine ⟨79037931447240506709579569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52691954298160337806386379 79037931447240506709579569)
    ·
      refine ⟨59278448585430380032184677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79037931447240506709579569 59278448585430380032184677)
      ·
        refine ⟨11114709109768196256034627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59278448585430380032184677 11114709109768196256034627)
        ·
          refine ⟨16672063664652294384051941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11114709109768196256034627 16672063664652294384051941)
          ·
            refine ⟨3126011937122305197009739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16672063664652294384051941 3126011937122305197009739)
            ·
              refine ⟨4689017905683457795514609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3126011937122305197009739 4689017905683457795514609)
              ·
                refine ⟨3516763429262593346635957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4689017905683457795514609 3516763429262593346635957)
                ·
                  refine ⟨329696571493368126247121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3516763429262593346635957 329696571493368126247121)
                  ·
                    rfl

theorem cell22_2889368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 5].length) (baseStart_2889368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889368 prefixEnd_2889368 := by exact prefixLift 2889368
  have htrace : WordTrace (prefixWord ++ tailWord_2889368) baseStart_2889368 baseEnd_2889368 := by
    simpa [prefixWord, tailWord_2889368, baseEnd_2889368] using wordTrace_append hprefix tailTrace_2889368
  have hstable : (prefixWord ++ tailWord_2889368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889368).length < 2 ^ (prefixWord ++ tailWord_2889368).sum := by decide
  have hdescent : baseEnd_2889368 < baseStart_2889368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889486 : List Nat := [4, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_2889486 : Nat := 118140960795 + 2889486 * 2 ^ 59
def prefixEnd_2889486 : Nat := 4983230072969 + 3 ^ 40 * 2889486 * 2
def baseEnd_2889486 : Nat := 329710036097197134763667

theorem tailTrace_2889486 : CollatzResearch.WordTrace tailWord_2889486 prefixEnd_2889486 329710036097197134763667 := by
  unfold tailWord_2889486
  simp only [CollatzResearch.WordTrace]
  refine ⟨13173526551236647720696039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70258808273262121177045541 13173526551236647720696039)
  ·
    refine ⟨19760289826854971581044059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13173526551236647720696039 19760289826854971581044059)
    ·
      refine ⟨29640434740282457371566089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19760289826854971581044059 29640434740282457371566089)
      ·
        refine ⟨22230326055211843028674567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29640434740282457371566089 22230326055211843028674567)
        ·
          refine ⟨33345489082817764543011851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22230326055211843028674567 33345489082817764543011851)
          ·
            refine ⟨50018233624226646814517777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33345489082817764543011851 50018233624226646814517777)
            ·
              refine ⟨37513675218169985110888333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50018233624226646814517777 37513675218169985110888333)
              ·
                refine ⟨14067628206813744416583125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37513675218169985110888333 14067628206813744416583125)
                ·
                  refine ⟨329710036097197134763667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14067628206813744416583125 329710036097197134763667)
                  ·
                    rfl

theorem cell22_2889486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_2889486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889486 prefixEnd_2889486 := by exact prefixLift 2889486
  have htrace : WordTrace (prefixWord ++ tailWord_2889486) baseStart_2889486 baseEnd_2889486 := by
    simpa [prefixWord, tailWord_2889486, baseEnd_2889486] using wordTrace_append hprefix tailTrace_2889486
  have hstable : (prefixWord ++ tailWord_2889486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889486).length < 2 ^ (prefixWord ++ tailWord_2889486).sum := by decide
  have hdescent : baseEnd_2889486 < baseStart_2889486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889524 : List Nat := [2, 5, 1, 1, 2, 2, 2, 3, 1, 3]
def baseStart_2889524 : Nat := 118140960795 + 2889524 * 2 ^ 59
def prefixEnd_2889524 : Nat := 4983230072969 + 3 ^ 40 * 2889524 * 2
def baseEnd_2889524 : Nat := 989143116468171971840885

theorem tailTrace_2889524 : CollatzResearch.WordTrace tailWord_2889524 prefixEnd_2889524 989143116468171971840885 := by
  unfold tailWord_2889524
  simp only [CollatzResearch.WordTrace]
  refine ⟨52694799191877757127725813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70259732255837009503634417 52694799191877757127725813)
  ·
    refine ⟨4940137424238539730724295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 52694799191877757127725813 4940137424238539730724295)
    ·
      refine ⟨7410206136357809596086443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4940137424238539730724295 7410206136357809596086443)
      ·
        refine ⟨11115309204536714394129665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7410206136357809596086443 11115309204536714394129665)
        ·
          refine ⟨8336481903402535795597249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11115309204536714394129665 8336481903402535795597249)
          ·
            refine ⟨6252361427551901846697937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8336481903402535795597249 6252361427551901846697937)
            ·
              refine ⟨4689271070663926385023453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6252361427551901846697937 4689271070663926385023453)
              ·
                refine ⟨1758476651498972394383795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4689271070663926385023453 1758476651498972394383795)
                ·
                  refine ⟨2637714977248458591575693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758476651498972394383795 2637714977248458591575693)
                  ·
                    refine ⟨989143116468171971840885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2637714977248458591575693 989143116468171971840885)
                    ·
                      rfl

theorem cell22_2889524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_2889524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889524 prefixEnd_2889524 := by exact prefixLift 2889524
  have htrace : WordTrace (prefixWord ++ tailWord_2889524) baseStart_2889524 baseEnd_2889524 := by
    simpa [prefixWord, tailWord_2889524, baseEnd_2889524] using wordTrace_append hprefix tailTrace_2889524
  have hstable : (prefixWord ++ tailWord_2889524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889524).length < 2 ^ (prefixWord ++ tailWord_2889524).sum := by decide
  have hdescent : baseEnd_2889524 < baseStart_2889524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889561 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 3, 6]
def baseStart_2889561 : Nat := 118140960795 + 2889561 * 2 ^ 59
def prefixEnd_2889561 : Nat := 4983230072969 + 3 ^ 40 * 2889561 * 2
def baseEnd_2889561 : Nat := 989155782324316208665771

theorem tailTrace_2889561 : CollatzResearch.WordTrace tailWord_2889561 prefixEnd_2889561 989155782324316208665771 := by
  unfold tailWord_2889561
  simp only [CollatzResearch.WordTrace]
  refine ⟨105390947884621469574548537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70260631923080979716365691 105390947884621469574548537)
  ·
    refine ⟨79043210913466102180911403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105390947884621469574548537 79043210913466102180911403)
    ·
      refine ⟨118564816370199153271367105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79043210913466102180911403 118564816370199153271367105)
      ·
        refine ⟨88923612277649364953525329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118564816370199153271367105 88923612277649364953525329)
        ·
          refine ⟨66692709208237023715143997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88923612277649364953525329 66692709208237023715143997)
          ·
            refine ⟨25009765953088883893178999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66692709208237023715143997 25009765953088883893178999)
            ·
              refine ⟨37514648929633325839768499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25009765953088883893178999 37514648929633325839768499)
              ·
                refine ⟨56271973394449988759652749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37514648929633325839768499 56271973394449988759652749)
                ·
                  refine ⟨21101990022918745784869781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56271973394449988759652749 21101990022918745784869781)
                  ·
                    refine ⟨989155782324316208665771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21101990022918745784869781 989155782324316208665771)
                    ·
                      rfl

theorem cell22_2889561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 3, 6].length) (baseStart_2889561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889561 prefixEnd_2889561 := by exact prefixLift 2889561
  have htrace : WordTrace (prefixWord ++ tailWord_2889561) baseStart_2889561 baseEnd_2889561 := by
    simpa [prefixWord, tailWord_2889561, baseEnd_2889561] using wordTrace_append hprefix tailTrace_2889561
  have hstable : (prefixWord ++ tailWord_2889561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889561).length < 2 ^ (prefixWord ++ tailWord_2889561).sum := by decide
  have hdescent : baseEnd_2889561 < baseStart_2889561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889582 : List Nat := [4, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_2889582 : Nat := 118140960795 + 2889582 * 2 ^ 59
def prefixEnd_2889582 : Nat := 4983230072969 + 3 ^ 40 * 2889582 * 2
def baseEnd_2889582 : Nat := 329720990351159717963569

theorem tailTrace_2889582 : CollatzResearch.WordTrace tailWord_2889582 prefixEnd_2889582 329720990351159717963569 := by
  unfold tailWord_2889582
  simp only [CollatzResearch.WordTrace]
  refine ⟨13173964227193173770132875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70261142545030260107375333 13173964227193173770132875)
  ·
    refine ⟨19760946340789760655199313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13173964227193173770132875 19760946340789760655199313)
    ·
      refine ⟨14820709755592320491399485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19760946340789760655199313 14820709755592320491399485)
      ·
        refine ⟨5557766158347120184274807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14820709755592320491399485 5557766158347120184274807)
        ·
          refine ⟨8336649237520680276412211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5557766158347120184274807 8336649237520680276412211)
          ·
            refine ⟨12504973856281020414618317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8336649237520680276412211 12504973856281020414618317)
            ·
              refine ⟨4689365196105382655481869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12504973856281020414618317 4689365196105382655481869)
              ·
                refine ⟨1758511948539518495805701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4689365196105382655481869 1758511948539518495805701)
                ·
                  refine ⟨329720990351159717963569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1758511948539518495805701 329720990351159717963569)
                  ·
                    rfl

theorem cell22_2889582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_2889582 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889582 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889582 prefixEnd_2889582 := by exact prefixLift 2889582
  have htrace : WordTrace (prefixWord ++ tailWord_2889582) baseStart_2889582 baseEnd_2889582 := by
    simpa [prefixWord, tailWord_2889582, baseEnd_2889582] using wordTrace_append hprefix tailTrace_2889582
  have hstable : (prefixWord ++ tailWord_2889582).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889582).length < 2 ^ (prefixWord ++ tailWord_2889582).sum := by decide
  have hdescent : baseEnd_2889582 < baseStart_2889582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889610 : List Nat := [3, 1, 2, 4, 2, 1, 2, 7]
def baseStart_2889610 : Nat := 118140960795 + 2889610 * 2 ^ 59
def prefixEnd_2889610 : Nat := 4983230072969 + 3 ^ 40 * 2889610 * 2
def baseEnd_2889610 : Nat := 109908061780632934910069

theorem tailTrace_2889610 : CollatzResearch.WordTrace tailWord_2889610 prefixEnd_2889610 109908061780632934910069 := by
  unfold tailWord_2889610
  simp only [CollatzResearch.WordTrace]
  refine ⟨26348183765360987735770571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70261823374295967295388189 26348183765360987735770571)
  ·
    refine ⟨39522275648041481603655857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26348183765360987735770571 39522275648041481603655857)
    ·
      refine ⟨29641706736031111202741893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39522275648041481603655857 29641706736031111202741893)
      ·
        refine ⟨5557820013005833350514105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29641706736031111202741893 5557820013005833350514105)
        ·
          refine ⟨4168365009754375012885579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5557820013005833350514105 4168365009754375012885579)
          ·
            refine ⟨6252547514631562519328369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168365009754375012885579 6252547514631562519328369)
            ·
              refine ⟨4689410635973671889496277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6252547514631562519328369 4689410635973671889496277)
              ·
                refine ⟨109908061780632934910069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4689410635973671889496277 109908061780632934910069)
                ·
                  rfl

theorem cell22_2889610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 7].length) (baseStart_2889610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889610 prefixEnd_2889610 := by exact prefixLift 2889610
  have htrace : WordTrace (prefixWord ++ tailWord_2889610) baseStart_2889610 baseEnd_2889610 := by
    simpa [prefixWord, tailWord_2889610, baseEnd_2889610] using wordTrace_append hprefix tailTrace_2889610
  have hstable : (prefixWord ++ tailWord_2889610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889610).length < 2 ^ (prefixWord ++ tailWord_2889610).sum := by decide
  have hdescent : baseEnd_2889610 < baseStart_2889610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889614 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 2, 3]
def baseStart_2889614 : Nat := 118140960795 + 2889614 * 2 ^ 59
def prefixEnd_2889614 : Nat := 4983230072969 + 3 ^ 40 * 2889614 * 2
def baseEnd_2889614 : Nat := 989173925307441737090609

theorem tailTrace_2889614 : CollatzResearch.WordTrace tailWord_2889614 prefixEnd_2889614 989173925307441737090609 := by
  unfold tailWord_2889614
  simp only [CollatzResearch.WordTrace]
  refine ⟨13174110119178682453278487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70261920635619639750818597 13174110119178682453278487)
  ·
    refine ⟨19761165178768023679917731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13174110119178682453278487 19761165178768023679917731)
    ·
      refine ⟨29641747768152035519876597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19761165178768023679917731 29641747768152035519876597)
      ·
        refine ⟨2778913853264253329988431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29641747768152035519876597 2778913853264253329988431)
        ·
          refine ⟨4168370779896379994982647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778913853264253329988431 4168370779896379994982647)
          ·
            refine ⟨6252556169844569992473971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168370779896379994982647 6252556169844569992473971)
            ·
              refine ⟨9378834254766854988710957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6252556169844569992473971 9378834254766854988710957)
              ·
                refine ⟨3517062845537570620766609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9378834254766854988710957 3517062845537570620766609)
                ·
                  refine ⟨2637797134153177965574957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3517062845537570620766609 2637797134153177965574957)
                  ·
                    refine ⟨989173925307441737090609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2637797134153177965574957 989173925307441737090609)
                    ·
                      rfl

theorem cell22_2889614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 2, 3].length) (baseStart_2889614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889614 prefixEnd_2889614 := by exact prefixLift 2889614
  have htrace : WordTrace (prefixWord ++ tailWord_2889614) baseStart_2889614 baseEnd_2889614 := by
    simpa [prefixWord, tailWord_2889614, baseEnd_2889614] using wordTrace_append hprefix tailTrace_2889614
  have hstable : (prefixWord ++ tailWord_2889614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889614).length < 2 ^ (prefixWord ++ tailWord_2889614).sum := by decide
  have hdescent : baseEnd_2889614 < baseStart_2889614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889685 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 3, 4]
def baseStart_2889685 : Nat := 118140960795 + 2889685 * 2 ^ 59
def prefixEnd_2889685 : Nat := 4983230072969 + 3 ^ 40 * 2889685 * 2
def baseEnd_2889685 : Nat := 989198230058421218565391

theorem tailTrace_2889685 : CollatzResearch.WordTrace tailWord_2889685 prefixEnd_2889685 989198230058421218565391 := by
  unfold tailWord_2889685
  simp only [CollatzResearch.WordTrace]
  refine ⟨105395470536172238752062509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70263647024114825834708339 105395470536172238752062509)
  ·
    refine ⟨39523301451064589532023441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105395470536172238752062509 39523301451064589532023441)
    ·
      refine ⟨29642476088298442149017581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39523301451064589532023441 29642476088298442149017581)
      ·
        refine ⟨11115928533111915805881593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29642476088298442149017581 11115928533111915805881593)
        ·
          refine ⟨8336946399833936854411195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11115928533111915805881593 8336946399833936854411195)
          ·
            refine ⟨12505419599750905281616793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8336946399833936854411195 12505419599750905281616793)
            ·
              refine ⟨9379064699813178961212595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12505419599750905281616793 9379064699813178961212595)
              ·
                refine ⟨14068597049719768441818893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9379064699813178961212595 14068597049719768441818893)
                ·
                  refine ⟨5275723893644913165682085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14068597049719768441818893 5275723893644913165682085)
                  ·
                    refine ⟨989198230058421218565391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5275723893644913165682085 989198230058421218565391)
                    ·
                      rfl

theorem cell22_2889685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_2889685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889685 prefixEnd_2889685 := by exact prefixLift 2889685
  have htrace : WordTrace (prefixWord ++ tailWord_2889685) baseStart_2889685 baseEnd_2889685 := by
    simpa [prefixWord, tailWord_2889685, baseEnd_2889685] using wordTrace_append hprefix tailTrace_2889685
  have hstable : (prefixWord ++ tailWord_2889685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889685).length < 2 ^ (prefixWord ++ tailWord_2889685).sum := by decide
  have hdescent : baseEnd_2889685 < baseStart_2889685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889751 : List Nat := [1, 1, 3, 5, 3, 1, 1, 3, 4]
def baseStart_2889751 : Nat := 118140960795 + 2889751 * 2 ^ 59
def prefixEnd_2889751 : Nat := 4983230072969 + 3 ^ 40 * 2889751 * 2
def baseEnd_2889751 : Nat := 329740274402406348805063

theorem tailTrace_2889751 : CollatzResearch.WordTrace tailWord_2889751 prefixEnd_2889751 329740274402406348805063 := by
  unfold tailWord_2889751
  simp only [CollatzResearch.WordTrace]
  refine ⟨105397877753933132023965107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70265251835955421349310071 105397877753933132023965107)
  ·
    refine ⟨158096816630899698035947661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105397877753933132023965107 158096816630899698035947661)
    ·
      refine ⟨59286306236587386763480373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158096816630899698035947661 59286306236587386763480373)
      ·
        refine ⟨5558091209680067509076285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59286306236587386763480373 5558091209680067509076285)
        ·
          refine ⟨2084284203630025315903607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5558091209680067509076285 2084284203630025315903607)
          ·
            refine ⟨3126426305445037973855411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2084284203630025315903607 3126426305445037973855411)
            ·
              refine ⟨4689639458167556960783117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3126426305445037973855411 4689639458167556960783117)
              ·
                refine ⟨1758614796812833860293669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4689639458167556960783117 1758614796812833860293669)
                ·
                  refine ⟨329740274402406348805063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1758614796812833860293669 329740274402406348805063)
                  ·
                    rfl

theorem cell22_2889751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 3, 4].length) (baseStart_2889751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889751 prefixEnd_2889751 := by exact prefixLift 2889751
  have htrace : WordTrace (prefixWord ++ tailWord_2889751) baseStart_2889751 baseEnd_2889751 := by
    simpa [prefixWord, tailWord_2889751, baseEnd_2889751] using wordTrace_append hprefix tailTrace_2889751
  have hstable : (prefixWord ++ tailWord_2889751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889751).length < 2 ^ (prefixWord ++ tailWord_2889751).sum := by decide
  have hdescent : baseEnd_2889751 < baseStart_2889751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889777 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 3, 3]
def baseStart_2889777 : Nat := 118140960795 + 2889777 * 2 ^ 59
def prefixEnd_2889777 : Nat := 4983230072969 + 3 ^ 40 * 2889777 * 2
def baseEnd_2889777 : Nat := 989229723538563645265109

theorem tailTrace_2889777 : CollatzResearch.WordTrace tailWord_2889777 prefixEnd_2889777 989229723538563645265109 := by
  unfold tailWord_2889777
  simp only [CollatzResearch.WordTrace]
  refine ⟨105398826051838938464411585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70265884034559292309607723 105398826051838938464411585)
  ·
    refine ⟨79049119538879203848308689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105398826051838938464411585 79049119538879203848308689)
    ·
      refine ⟨59286839654159402886231517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79049119538879203848308689 59286839654159402886231517)
      ·
        refine ⟨22232564870309776082336819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59286839654159402886231517 22232564870309776082336819)
        ·
          refine ⟨33348847305464664123505229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22232564870309776082336819 33348847305464664123505229)
          ·
            refine ⟨12505817739549249046314461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33348847305464664123505229 12505817739549249046314461)
            ·
              refine ⟨4689681652330968392367923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12505817739549249046314461 4689681652330968392367923)
              ·
                refine ⟨7034522478496452588551885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4689681652330968392367923 7034522478496452588551885)
                ·
                  refine ⟨2637945929436169720706957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7034522478496452588551885 2637945929436169720706957)
                  ·
                    refine ⟨989229723538563645265109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2637945929436169720706957 989229723538563645265109)
                    ·
                      rfl

theorem cell22_2889777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 3, 3].length) (baseStart_2889777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889777 prefixEnd_2889777 := by exact prefixLift 2889777
  have htrace : WordTrace (prefixWord ++ tailWord_2889777) baseStart_2889777 baseEnd_2889777 := by
    simpa [prefixWord, tailWord_2889777, baseEnd_2889777] using wordTrace_append hprefix tailTrace_2889777
  have hstable : (prefixWord ++ tailWord_2889777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889777).length < 2 ^ (prefixWord ++ tailWord_2889777).sum := by decide
  have hdescent : baseEnd_2889777 < baseStart_2889777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889803 : List Nat := [1, 1, 1, 1, 3, 1, 2, 2, 2, 8]
def baseStart_2889803 : Nat := 118140960795 + 2889803 * 2 ^ 59
def prefixEnd_2889803 : Nat := 4983230072969 + 3 ^ 40 * 2889803 * 2
def baseEnd_2889803 : Nat := 989238623869908244115029

theorem tailTrace_2889803 : CollatzResearch.WordTrace tailWord_2889803 prefixEnd_2889803 989238623869908244115029 := by
  unfold tailWord_2889803
  simp only [CollatzResearch.WordTrace]
  refine ⟨105399774349744744904858063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70266516233163163269905375 105399774349744744904858063)
  ·
    refine ⟨158099661524617117357287095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105399774349744744904858063 158099661524617117357287095)
    ·
      refine ⟨237149492286925676035930643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158099661524617117357287095 237149492286925676035930643)
      ·
        refine ⟨355724238430388514053895965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237149492286925676035930643 355724238430388514053895965)
        ·
          refine ⟨133396589411395692770210987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 355724238430388514053895965 133396589411395692770210987)
          ·
            refine ⟨200094884117093539155316481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133396589411395692770210987 200094884117093539155316481)
            ·
              refine ⟨150071163087820154366487361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200094884117093539155316481 150071163087820154366487361)
              ·
                refine ⟨112553372315865115774865521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150071163087820154366487361 112553372315865115774865521)
                ·
                  refine ⟨84415029236898836831149141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 112553372315865115774865521 84415029236898836831149141)
                  ·
                    refine ⟨989238623869908244115029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84415029236898836831149141 989238623869908244115029)
                    ·
                      rfl

theorem cell22_2889803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 2, 2, 8].length) (baseStart_2889803 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889803 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889803 prefixEnd_2889803 := by exact prefixLift 2889803
  have htrace : WordTrace (prefixWord ++ tailWord_2889803) baseStart_2889803 baseEnd_2889803 := by
    simpa [prefixWord, tailWord_2889803, baseEnd_2889803] using wordTrace_append hprefix tailTrace_2889803
  have hstable : (prefixWord ++ tailWord_2889803).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889803).length < 2 ^ (prefixWord ++ tailWord_2889803).sum := by decide
  have hdescent : baseEnd_2889803 < baseStart_2889803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889865 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 1, 6]
def baseStart_2889865 : Nat := 118140960795 + 2889865 * 2 ^ 59
def prefixEnd_2889865 : Nat := 4983230072969 + 3 ^ 40 * 2889865 * 2
def baseEnd_2889865 : Nat := 989259847736960749064839

theorem tailTrace_2889865 : CollatzResearch.WordTrace tailWord_2889865 prefixEnd_2889865 989259847736960749064839 := by
  unfold tailWord_2889865
  simp only [CollatzResearch.WordTrace]
  refine ⟨105402035675520129493615049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70268023783680086329076699 105402035675520129493615049)
  ·
    refine ⟨79051526756640097120211287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105402035675520129493615049 79051526756640097120211287)
    ·
      refine ⟨118577290134960145680316931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79051526756640097120211287 118577290134960145680316931)
      ·
        refine ⟨177865935202440218520475397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118577290134960145680316931 177865935202440218520475397)
        ·
          refine ⟨33349862850457540972589137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177865935202440218520475397 33349862850457540972589137)
          ·
            refine ⟨25012397137843155729441853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33349862850457540972589137 25012397137843155729441853)
            ·
              refine ⟨9379648926691183398540695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25012397137843155729441853 9379648926691183398540695)
              ·
                refine ⟨14069473390036775097811043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9379648926691183398540695 14069473390036775097811043)
                ·
                  refine ⟨21104210085055162646716565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14069473390036775097811043 21104210085055162646716565)
                  ·
                    refine ⟨989259847736960749064839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21104210085055162646716565 989259847736960749064839)
                    ·
                      rfl

theorem cell22_2889865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 1, 6].length) (baseStart_2889865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889865 prefixEnd_2889865 := by exact prefixLift 2889865
  have htrace : WordTrace (prefixWord ++ tailWord_2889865) baseStart_2889865 baseEnd_2889865 := by
    simpa [prefixWord, tailWord_2889865, baseEnd_2889865] using wordTrace_append hprefix tailTrace_2889865
  have hstable : (prefixWord ++ tailWord_2889865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889865).length < 2 ^ (prefixWord ++ tailWord_2889865).sum := by decide
  have hdescent : baseEnd_2889865 < baseStart_2889865 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889912 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 3, 3]
def baseStart_2889912 : Nat := 118140960795 + 2889912 * 2 ^ 59
def prefixEnd_2889912 : Nat := 4983230072969 + 3 ^ 40 * 2889912 * 2
def baseEnd_2889912 : Nat := 989275936797468293139695

theorem tailTrace_2889912 : CollatzResearch.WordTrace tailWord_2889912 prefixEnd_2889912 989275936797468293139695 := by
  unfold tailWord_2889912
  simp only [CollatzResearch.WordTrace]
  refine ⟨52701874953174928260287995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70269166604233237680383993 52701874953174928260287995)
  ·
    refine ⟨79052812429762392390431993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52701874953174928260287995 79052812429762392390431993)
    ·
      refine ⟨59289609322321794292823995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79052812429762392390431993 59289609322321794292823995)
      ·
        refine ⟨88934413983482691439235993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59289609322321794292823995 88934413983482691439235993)
        ·
          refine ⟨66700810487612018579426995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88934413983482691439235993 66700810487612018579426995)
          ·
            refine ⟨100051215731418027869140493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66700810487612018579426995 100051215731418027869140493)
            ·
              refine ⟨37519205899281760450927685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100051215731418027869140493 37519205899281760450927685)
              ·
                refine ⟨7034851106115330084548941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37519205899281760450927685 7034851106115330084548941)
                ·
                  refine ⟨2638069164793248781705853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7034851106115330084548941 2638069164793248781705853)
                  ·
                    refine ⟨989275936797468293139695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638069164793248781705853 989275936797468293139695)
                    ·
                      rfl

theorem cell22_2889912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_2889912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889912 prefixEnd_2889912 := by exact prefixLift 2889912
  have htrace : WordTrace (prefixWord ++ tailWord_2889912) baseStart_2889912 baseEnd_2889912 := by
    simpa [prefixWord, tailWord_2889912, baseEnd_2889912] using wordTrace_append hprefix tailTrace_2889912
  have hstable : (prefixWord ++ tailWord_2889912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889912).length < 2 ^ (prefixWord ++ tailWord_2889912).sum := by decide
  have hdescent : baseEnd_2889912 < baseStart_2889912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889925 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 7]
def baseStart_2889925 : Nat := 118140960795 + 2889925 * 2 ^ 59
def prefixEnd_2889925 : Nat := 4983230072969 + 3 ^ 40 * 2889925 * 2
def baseEnd_2889925 : Nat := 329760128987713530854885

theorem tailTrace_2889925 : CollatzResearch.WordTrace tailWord_2889925 prefixEnd_2889925 329760128987713530854885 := by
  unfold tailWord_2889925
  simp only [CollatzResearch.WordTrace]
  refine ⟨105404224055302759740799229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70269482703535173160532819 105404224055302759740799229)
  ·
    refine ⟨39526584020738534902799711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105404224055302759740799229 39526584020738534902799711)
    ·
      refine ⟨59289876031107802354199567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39526584020738534902799711 59289876031107802354199567)
      ·
        refine ⟨88934814046661703531299351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59289876031107802354199567 88934814046661703531299351)
        ·
          refine ⟨133402221069992555296949027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88934814046661703531299351 133402221069992555296949027)
          ·
            refine ⟨200103331604988832945423541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133402221069992555296949027 200103331604988832945423541)
            ·
              refine ⟨18759687337967703088633457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 200103331604988832945423541 18759687337967703088633457)
              ·
                refine ⟨14069765503475777316475093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18759687337967703088633457 14069765503475777316475093)
                ·
                  refine ⟨329760128987713530854885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14069765503475777316475093 329760128987713530854885)
                  ·
                    rfl

theorem cell22_2889925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_2889925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889925 prefixEnd_2889925 := by exact prefixLift 2889925
  have htrace : WordTrace (prefixWord ++ tailWord_2889925) baseStart_2889925 baseEnd_2889925 := by
    simpa [prefixWord, tailWord_2889925, baseEnd_2889925] using wordTrace_append hprefix tailTrace_2889925
  have hstable : (prefixWord ++ tailWord_2889925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889925).length < 2 ^ (prefixWord ++ tailWord_2889925).sum := by decide
  have hdescent : baseEnd_2889925 < baseStart_2889925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889929 : List Nat := [1, 2, 1, 1, 2, 1, 1, 9, 1, 3]
def baseStart_2889929 : Nat := 118140960795 + 2889929 * 2 ^ 59
def prefixEnd_2889929 : Nat := 4983230072969 + 3 ^ 40 * 2889929 * 2
def baseEnd_2889929 : Nat := 989281756244885915464643

theorem tailTrace_2889929 : CollatzResearch.WordTrace tailWord_2889929 prefixEnd_2889929 989281756244885915464643 := by
  unfold tailWord_2889929
  simp only [CollatzResearch.WordTrace]
  refine ⟨105404369947288268423944841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70269579964858845615963227 105404369947288268423944841)
  ·
    refine ⟨79053277460466201317958631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105404369947288268423944841 79053277460466201317958631)
    ·
      refine ⟨118579916190699301976937947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79053277460466201317958631 118579916190699301976937947)
      ·
        refine ⟨177869874286048952965406921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118579916190699301976937947 177869874286048952965406921)
        ·
          refine ⟨133402405714536714724055191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 177869874286048952965406921 133402405714536714724055191)
          ·
            refine ⟨200103608571805072086082787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133402405714536714724055191 200103608571805072086082787)
            ·
              refine ⟨300155412857707608129124181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 200103608571805072086082787 300155412857707608129124181)
              ·
                refine ⟨1758723122213130516381587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 300155412857707608129124181 1758723122213130516381587)
                ·
                  refine ⟨2638084683319695774572381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758723122213130516381587 2638084683319695774572381)
                  ·
                    refine ⟨989281756244885915464643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638084683319695774572381 989281756244885915464643)
                    ·
                      rfl

theorem cell22_2889929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 1, 3].length) (baseStart_2889929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889929 prefixEnd_2889929 := by exact prefixLift 2889929
  have htrace : WordTrace (prefixWord ++ tailWord_2889929) baseStart_2889929 baseEnd_2889929 := by
    simpa [prefixWord, tailWord_2889929, baseEnd_2889929] using wordTrace_append hprefix tailTrace_2889929
  have hstable : (prefixWord ++ tailWord_2889929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889929).length < 2 ^ (prefixWord ++ tailWord_2889929).sum := by decide
  have hdescent : baseEnd_2889929 < baseStart_2889929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2889959 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 5]
def baseStart_2889959 : Nat := 118140960795 + 2889959 * 2 ^ 59
def prefixEnd_2889959 : Nat := 4983230072969 + 3 ^ 40 * 2889959 * 2
def baseEnd_2889959 : Nat := 329764008619325279071517

theorem tailTrace_2889959 : CollatzResearch.WordTrace tailWord_2889959 prefixEnd_2889959 329764008619325279071517 := by
  unfold tailWord_2889959
  simp only [CollatzResearch.WordTrace]
  refine ⟨105405464137179583547536931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70270309424786389031691287 105405464137179583547536931)
  ·
    refine ⟨158108196205769375321305397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105405464137179583547536931 158108196205769375321305397)
    ·
      refine ⟨14822643394290878936372381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 158108196205769375321305397 14822643394290878936372381)
      ·
        refine ⟨5558491272859079601139643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14822643394290878936372381 5558491272859079601139643)
        ·
          refine ⟨8337736909288619401709465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5558491272859079601139643 8337736909288619401709465)
          ·
            refine ⟨6253302681966464551282099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8337736909288619401709465 6253302681966464551282099)
            ·
              refine ⟨9379954022949696826923149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6253302681966464551282099 9379954022949696826923149)
              ·
                refine ⟨3517482758606136310096181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9379954022949696826923149 3517482758606136310096181)
                ·
                  refine ⟨329764008619325279071517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3517482758606136310096181 329764008619325279071517)
                  ·
                    rfl

theorem cell22_2889959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 5].length) (baseStart_2889959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2889959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2889959 prefixEnd_2889959 := by exact prefixLift 2889959
  have htrace : WordTrace (prefixWord ++ tailWord_2889959) baseStart_2889959 baseEnd_2889959 := by
    simpa [prefixWord, tailWord_2889959, baseEnd_2889959] using wordTrace_append hprefix tailTrace_2889959
  have hstable : (prefixWord ++ tailWord_2889959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2889959).length < 2 ^ (prefixWord ++ tailWord_2889959).sum := by decide
  have hdescent : baseEnd_2889959 < baseStart_2889959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2889959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890017 : List Nat := [1, 2, 3, 2, 1, 1, 2, 2, 4, 4]
def baseStart_2890017 : Nat := 118140960795 + 2890017 * 2 ^ 59
def prefixEnd_2890017 : Nat := 4983230072969 + 3 ^ 40 * 2890017 * 2
def baseEnd_2890017 : Nat := 989311880443283019264373

theorem tailTrace_2890017 : CollatzResearch.WordTrace tailWord_2890017 prefixEnd_2890017 989311880443283019264373 := by
  unfold tailWord_2890017
  simp only [CollatzResearch.WordTrace]
  refine ⟨105407579570969459453148305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70271719713979639635432203 105407579570969459453148305)
  ·
    refine ⟨79055684678227094589861229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105407579570969459453148305 79055684678227094589861229)
    ·
      refine ⟨29645881754335160471197961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79055684678227094589861229 29645881754335160471197961)
      ·
        refine ⟨22234411315751370353398471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29645881754335160471197961 22234411315751370353398471)
        ·
          refine ⟨33351616973627055530097707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22234411315751370353398471 33351616973627055530097707)
          ·
            refine ⟨50027425460440583295146561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33351616973627055530097707 50027425460440583295146561)
            ·
              refine ⟨37520569095330437471359921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50027425460440583295146561 37520569095330437471359921)
              ·
                refine ⟨28140426821497828103519941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37520569095330437471359921 28140426821497828103519941)
                ·
                  refine ⟨5276330029030842769409989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28140426821497828103519941 5276330029030842769409989)
                  ·
                    refine ⟨989311880443283019264373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5276330029030842769409989 989311880443283019264373)
                    ·
                      rfl

theorem cell22_2890017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 2, 4, 4].length) (baseStart_2890017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890017 prefixEnd_2890017 := by exact prefixLift 2890017
  have htrace : WordTrace (prefixWord ++ tailWord_2890017) baseStart_2890017 baseEnd_2890017 := by
    simpa [prefixWord, tailWord_2890017, baseEnd_2890017] using wordTrace_append hprefix tailTrace_2890017
  have hstable : (prefixWord ++ tailWord_2890017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890017).length < 2 ^ (prefixWord ++ tailWord_2890017).sum := by decide
  have hdescent : baseEnd_2890017 < baseStart_2890017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890019 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 2, 3]
def baseStart_2890019 : Nat := 118140960795 + 2890019 * 2 ^ 59
def prefixEnd_2890019 : Nat := 4983230072969 + 3 ^ 40 * 2890019 * 2
def baseEnd_2890019 : Nat := 989312565084155680714367

theorem tailTrace_2890019 : CollatzResearch.WordTrace tailWord_2890019 prefixEnd_2890019 989312565084155680714367 := by
  unfold tailWord_2890019
  simp only [CollatzResearch.WordTrace]
  refine ⟨105407652516962213794721111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70271768344641475863147407 105407652516962213794721111)
  ·
    refine ⟨158111478775443320692081667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105407652516962213794721111 158111478775443320692081667)
    ·
      refine ⟨237167218163164981038122501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158111478775443320692081667 237167218163164981038122501)
      ·
        refine ⟨44468853405593433944647969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 237167218163164981038122501 44468853405593433944647969)
        ·
          refine ⟨33351640054195075458485977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44468853405593433944647969 33351640054195075458485977)
          ·
            refine ⟨25013730040646306593864483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33351640054195075458485977 25013730040646306593864483)
            ·
              refine ⟨37520595060969459890796725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25013730040646306593864483 37520595060969459890796725)
              ·
                refine ⟨3517555786965886864762193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37520595060969459890796725 3517555786965886864762193)
                ·
                  refine ⟨2638166840224415148571645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3517555786965886864762193 2638166840224415148571645)
                  ·
                    refine ⟨989312565084155680714367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638166840224415148571645 989312565084155680714367)
                    ·
                      rfl

theorem cell22_2890019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 2, 3].length) (baseStart_2890019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890019 prefixEnd_2890019 := by exact prefixLift 2890019
  have htrace : WordTrace (prefixWord ++ tailWord_2890019) baseStart_2890019 baseEnd_2890019 := by
    simpa [prefixWord, tailWord_2890019, baseEnd_2890019] using wordTrace_append hprefix tailTrace_2890019
  have hstable : (prefixWord ++ tailWord_2890019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890019).length < 2 ^ (prefixWord ++ tailWord_2890019).sum := by decide
  have hdescent : baseEnd_2890019 < baseStart_2890019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890034 : List Nat := [3, 2, 1, 1, 5, 1, 1, 1, 1, 6]
def baseStart_2890034 : Nat := 118140960795 + 2890034 * 2 ^ 59
def prefixEnd_2890034 : Nat := 4983230072969 + 3 ^ 40 * 2890034 * 2
def baseEnd_2890034 : Nat := 989317699890700641589321

theorem tailTrace_2890034 : CollatzResearch.WordTrace tailWord_2890034 prefixEnd_2890034 989317699890700641589321 := by
  unfold tailWord_2890034
  simp only [CollatzResearch.WordTrace]
  refine ⟨26352049902976967839129289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70272133074605247571011437 26352049902976967839129289)
  ·
    refine ⟨19764037427232725879346967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26352049902976967839129289 19764037427232725879346967)
    ·
      refine ⟨29646056140849088819020451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19764037427232725879346967 29646056140849088819020451)
      ·
        refine ⟨44469084211273633228530677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29646056140849088819020451 44469084211273633228530677)
        ·
          refine ⟨4168976644806903115174751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44469084211273633228530677 4168976644806903115174751)
          ·
            refine ⟨6253464967210354672762127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168976644806903115174751 6253464967210354672762127)
            ·
              refine ⟨9380197450815532009143191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6253464967210354672762127 9380197450815532009143191)
              ·
                refine ⟨14070296176223298013714787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9380197450815532009143191 14070296176223298013714787)
                ·
                  refine ⟨21105444264334947020572181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14070296176223298013714787 21105444264334947020572181)
                  ·
                    refine ⟨989317699890700641589321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21105444264334947020572181 989317699890700641589321)
                    ·
                      rfl

theorem cell22_2890034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 1, 1, 1, 6].length) (baseStart_2890034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890034 prefixEnd_2890034 := by exact prefixLift 2890034
  have htrace : WordTrace (prefixWord ++ tailWord_2890034) baseStart_2890034 baseEnd_2890034 := by
    simpa [prefixWord, tailWord_2890034, baseEnd_2890034] using wordTrace_append hprefix tailTrace_2890034
  have hstable : (prefixWord ++ tailWord_2890034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890034).length < 2 ^ (prefixWord ++ tailWord_2890034).sum := by decide
  have hdescent : baseEnd_2890034 < baseStart_2890034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890049 : List Nat := [1, 2, 5, 2, 2, 1, 9]
def baseStart_2890049 : Nat := 118140960795 + 2890049 * 2 ^ 59
def prefixEnd_2890049 : Nat := 4983230072969 + 3 ^ 40 * 2890049 * 2
def baseEnd_2890049 : Nat := 36641586470268355646825

theorem tailTrace_2890049 : CollatzResearch.WordTrace tailWord_2890049 prefixEnd_2890049 36641586470268355646825 := by
  unfold tailWord_2890049
  simp only [CollatzResearch.WordTrace]
  refine ⟨105408746706853528918313201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70272497804569019278875467 105408746706853528918313201)
  ·
    refine ⟨79056560030140146688734901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105408746706853528918313201 79056560030140146688734901)
    ·
      refine ⟨7411552502825638752068897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79056560030140146688734901 7411552502825638752068897)
      ·
        refine ⟨5558664377119229064051673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7411552502825638752068897 5558664377119229064051673)
        ·
          refine ⟨4168998282839421798038755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5558664377119229064051673 4168998282839421798038755)
          ·
            refine ⟨6253497424259132697058133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4168998282839421798038755 6253497424259132697058133)
            ·
              refine ⟨36641586470268355646825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6253497424259132697058133 36641586470268355646825)
              ·
                rfl

theorem cell22_2890049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 9].length) (baseStart_2890049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890049 prefixEnd_2890049 := by exact prefixLift 2890049
  have htrace : WordTrace (prefixWord ++ tailWord_2890049) baseStart_2890049 baseEnd_2890049 := by
    simpa [prefixWord, tailWord_2890049, baseEnd_2890049] using wordTrace_append hprefix tailTrace_2890049
  have hstable : (prefixWord ++ tailWord_2890049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890049).length < 2 ^ (prefixWord ++ tailWord_2890049).sum := by decide
  have hdescent : baseEnd_2890049 < baseStart_2890049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890062 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 2, 6]
def baseStart_2890062 : Nat := 118140960795 + 2890062 * 2 ^ 59
def prefixEnd_2890062 : Nat := 4983230072969 + 3 ^ 40 * 2890062 * 2
def baseEnd_2890062 : Nat := 989327284862917901889235

theorem tailTrace_2890062 : CollatzResearch.WordTrace tailWord_2890062 prefixEnd_2890062 989327284862917901889235 := by
  unfold tailWord_2890062
  simp only [CollatzResearch.WordTrace]
  refine ⟨13176152606975804017317055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70272813903870954759024293 13176152606975804017317055)
  ·
    refine ⟨19764228910463706025975583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13176152606975804017317055 19764228910463706025975583)
    ·
      refine ⟨29646343365695559038963375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19764228910463706025975583 29646343365695559038963375)
      ·
        refine ⟨44469515048543338558445063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29646343365695559038963375 44469515048543338558445063)
        ·
          refine ⟨66704272572815007837667595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44469515048543338558445063 66704272572815007837667595)
          ·
            refine ⟨100056408859222511756501393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66704272572815007837667595 100056408859222511756501393)
            ·
              refine ⟨75042306644416883817376045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100056408859222511756501393 75042306644416883817376045)
              ·
                refine ⟨28140864991656331431516017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75042306644416883817376045 28140864991656331431516017)
                ·
                  refine ⟨21105648743742248573637013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28140864991656331431516017 21105648743742248573637013)
                  ·
                    refine ⟨989327284862917901889235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21105648743742248573637013 989327284862917901889235)
                    ·
                      rfl

theorem cell22_2890062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_2890062 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890062 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890062 prefixEnd_2890062 := by exact prefixLift 2890062
  have htrace : WordTrace (prefixWord ++ tailWord_2890062) baseStart_2890062 baseEnd_2890062 := by
    simpa [prefixWord, tailWord_2890062, baseEnd_2890062] using wordTrace_append hprefix tailTrace_2890062
  have hstable : (prefixWord ++ tailWord_2890062).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890062).length < 2 ^ (prefixWord ++ tailWord_2890062).sum := by decide
  have hdescent : baseEnd_2890062 < baseStart_2890062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890064 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 3, 3]
def baseStart_2890064 : Nat := 118140960795 + 2890064 * 2 ^ 59
def prefixEnd_2890064 : Nat := 4983230072969 + 3 ^ 40 * 2890064 * 2
def baseEnd_2890064 : Nat := 989327969503790563339229

theorem tailTrace_2890064 : CollatzResearch.WordTrace tailWord_2890064 prefixEnd_2890064 989327969503790563339229 := by
  unfold tailWord_2890064
  simp only [CollatzResearch.WordTrace]
  refine ⟨52704646900899593240054623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70272862534532790986739497 52704646900899593240054623)
  ·
    refine ⟨79056970351349389860081935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52704646900899593240054623 79056970351349389860081935)
    ·
      refine ⟨118585455527024084790122903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79056970351349389860081935 118585455527024084790122903)
      ·
        refine ⟨177878183290536127185184355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118585455527024084790122903 177878183290536127185184355)
        ·
          refine ⟨266817274935804190777776533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177878183290536127185184355 266817274935804190777776533)
          ·
            refine ⟨12507059762615821442708275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 266817274935804190777776533 12507059762615821442708275)
            ·
              refine ⟨18760589643923732164062413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12507059762615821442708275 18760589643923732164062413)
              ·
                refine ⟨7035221116471399561523405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18760589643923732164062413 7035221116471399561523405)
                ·
                  refine ⟨2638207918676774835571277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7035221116471399561523405 2638207918676774835571277)
                  ·
                    refine ⟨989327969503790563339229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638207918676774835571277 989327969503790563339229)
                    ·
                      rfl

theorem cell22_2890064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 3, 3].length) (baseStart_2890064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890064 prefixEnd_2890064 := by exact prefixLift 2890064
  have htrace : WordTrace (prefixWord ++ tailWord_2890064) baseStart_2890064 baseEnd_2890064 := by
    simpa [prefixWord, tailWord_2890064, baseEnd_2890064] using wordTrace_append hprefix tailTrace_2890064
  have hstable : (prefixWord ++ tailWord_2890064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890064).length < 2 ^ (prefixWord ++ tailWord_2890064).sum := by decide
  have hdescent : baseEnd_2890064 < baseStart_2890064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890098 : List Nat := [3, 2, 1, 2, 1, 3, 3, 3, 1, 3]
def baseStart_2890098 : Nat := 118140960795 + 2890098 * 2 ^ 59
def prefixEnd_2890098 : Nat := 4983230072969 + 3 ^ 40 * 2890098 * 2
def baseEnd_2890098 : Nat := 989339608398625807989125

theorem tailTrace_2890098 : CollatzResearch.WordTrace tailWord_2890098 prefixEnd_2890098 989339608398625807989125 := by
  unfold tailWord_2890098
  simp only [CollatzResearch.WordTrace]
  refine ⟨26352633470919002571711737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70273689255784006857897965 26352633470919002571711737)
  ·
    refine ⟨19764475103189251928783803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26352633470919002571711737 19764475103189251928783803)
    ·
      refine ⟨29646712654783877893175705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19764475103189251928783803 29646712654783877893175705)
      ·
        refine ⟨22235034491087908419881779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29646712654783877893175705 22235034491087908419881779)
        ·
          refine ⟨33352551736631862629822669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22235034491087908419881779 33352551736631862629822669)
          ·
            refine ⟨12507206901236948486183501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33352551736631862629822669 12507206901236948486183501)
            ·
              refine ⟨4690202587963855682318813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12507206901236948486183501 4690202587963855682318813)
              ·
                refine ⟨1758825970486445880869555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4690202587963855682318813 1758825970486445880869555)
                ·
                  refine ⟨2638238955729668821304333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758825970486445880869555 2638238955729668821304333)
                  ·
                    refine ⟨989339608398625807989125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638238955729668821304333 989339608398625807989125)
                    ·
                      rfl

theorem cell22_2890098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 1, 3].length) (baseStart_2890098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890098 prefixEnd_2890098 := by exact prefixLift 2890098
  have htrace : WordTrace (prefixWord ++ tailWord_2890098) baseStart_2890098 baseEnd_2890098 := by
    simpa [prefixWord, tailWord_2890098, baseEnd_2890098] using wordTrace_append hprefix tailTrace_2890098
  have hstable : (prefixWord ++ tailWord_2890098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890098).length < 2 ^ (prefixWord ++ tailWord_2890098).sum := by decide
  have hdescent : baseEnd_2890098 < baseStart_2890098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890115 : List Nat := [1, 1, 1, 3, 6, 1, 3, 2, 1, 3]
def baseStart_2890115 : Nat := 118140960795 + 2890115 * 2 ^ 59
def prefixEnd_2890115 : Nat := 4983230072969 + 3 ^ 40 * 2890115 * 2
def baseEnd_2890115 : Nat := 989345427846043430314073

theorem tailTrace_2890115 : CollatzResearch.WordTrace tailWord_2890115 prefixEnd_2890115 989345427846043430314073 := by
  unfold tailWord_2890115
  simp only [CollatzResearch.WordTrace]
  refine ⟨105411153924614422190215799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70274102616409614793477199 105411153924614422190215799)
  ·
    refine ⟨158116730886921633285323699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105411153924614422190215799 158116730886921633285323699)
    ·
      refine ⟨237175096330382449927985549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158116730886921633285323699 237175096330382449927985549)
      ·
        refine ⟨88940661123893418722994581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237175096330382449927985549 88940661123893418722994581)
        ·
          refine ⟨4169093490182504002640371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88940661123893418722994581 4169093490182504002640371)
          ·
            refine ⟨6253640235273756003960557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4169093490182504002640371 6253640235273756003960557)
            ·
              refine ⟨2345115088227658501485209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6253640235273756003960557 2345115088227658501485209)
              ·
                refine ⟨1758836316170743876113907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2345115088227658501485209 1758836316170743876113907)
                ·
                  refine ⟨2638254474256115814170861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758836316170743876113907 2638254474256115814170861)
                  ·
                    refine ⟨989345427846043430314073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638254474256115814170861 989345427846043430314073)
                    ·
                      rfl

theorem cell22_2890115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 1, 3].length) (baseStart_2890115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890115 prefixEnd_2890115 := by exact prefixLift 2890115
  have htrace : WordTrace (prefixWord ++ tailWord_2890115) baseStart_2890115 baseEnd_2890115 := by
    simpa [prefixWord, tailWord_2890115, baseEnd_2890115] using wordTrace_append hprefix tailTrace_2890115
  have hstable : (prefixWord ++ tailWord_2890115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890115).length < 2 ^ (prefixWord ++ tailWord_2890115).sum := by decide
  have hdescent : baseEnd_2890115 < baseStart_2890115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890141 : List Nat := [1, 4, 2, 1, 4, 1, 1, 1, 3, 4]
def baseStart_2890141 : Nat := 118140960795 + 2890141 * 2 ^ 59
def prefixEnd_2890141 : Nat := 4983230072969 + 3 ^ 40 * 2890141 * 2
def baseEnd_2890141 : Nat := 989354328177388029163993

theorem tailTrace_2890141 : CollatzResearch.WordTrace tailWord_2890141 prefixEnd_2890141 989354328177388029163993 := by
  unfold tailWord_2890141
  simp only [CollatzResearch.WordTrace]
  refine ⟨105412102222520228630662277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70274734815013485753774851 105412102222520228630662277)
  ·
    refine ⟨19764769166722542868249177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105412102222520228630662277 19764769166722542868249177)
    ·
      refine ⟨14823576875041907151186883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19764769166722542868249177 14823576875041907151186883)
      ·
        refine ⟨22235365312562860726780325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14823576875041907151186883 22235365312562860726780325)
        ·
          refine ⟨4169130996105536386271311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22235365312562860726780325 4169130996105536386271311)
          ·
            refine ⟨6253696494158304579406967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4169130996105536386271311 6253696494158304579406967)
            ·
              refine ⟨9380544741237456869110451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6253696494158304579406967 9380544741237456869110451)
              ·
                refine ⟨14070817111856185303665677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9380544741237456869110451 14070817111856185303665677)
                ·
                  refine ⟨5276556416946069488874629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14070817111856185303665677 5276556416946069488874629)
                  ·
                    refine ⟨989354328177388029163993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5276556416946069488874629 989354328177388029163993)
                    ·
                      rfl

theorem cell22_2890141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_2890141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890141 prefixEnd_2890141 := by exact prefixLift 2890141
  have htrace : WordTrace (prefixWord ++ tailWord_2890141) baseStart_2890141 baseEnd_2890141 := by
    simpa [prefixWord, tailWord_2890141, baseEnd_2890141] using wordTrace_append hprefix tailTrace_2890141
  have hstable : (prefixWord ++ tailWord_2890141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890141).length < 2 ^ (prefixWord ++ tailWord_2890141).sum := by decide
  have hdescent : baseEnd_2890141 < baseStart_2890141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890167 : List Nat := [1, 1, 3, 1, 3, 13]
def baseStart_2890167 : Nat := 118140960795 + 2890167 * 2 ^ 59
def prefixEnd_2890167 : Nat := 4983230072969 + 3 ^ 40 * 2890167 * 2
def baseEnd_2890167 : Nat := 12214360845786822568073

theorem tailTrace_2890167 : CollatzResearch.WordTrace tailWord_2890167 prefixEnd_2890167 12214360845786822568073 := by
  unfold tailWord_2890167
  simp only [CollatzResearch.WordTrace]
  refine ⟨105413050520426035071108755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70275367013617356714072503 105413050520426035071108755)
  ·
    refine ⟨158119575780639052606663133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105413050520426035071108755 158119575780639052606663133)
    ·
      refine ⟨59294840917739644727498675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 158119575780639052606663133 59294840917739644727498675)
      ·
        refine ⟨88942261376609467091248013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59294840917739644727498675 88942261376609467091248013)
        ·
          refine ⟨33353348016228550159218005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88942261376609467091248013 33353348016228550159218005)
          ·
            refine ⟨12214360845786822568073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 33353348016228550159218005 12214360845786822568073)
            ·
              rfl

theorem cell22_2890167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 13].length) (baseStart_2890167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890167 prefixEnd_2890167 := by exact prefixLift 2890167
  have htrace : WordTrace (prefixWord ++ tailWord_2890167) baseStart_2890167 baseEnd_2890167 := by
    simpa [prefixWord, tailWord_2890167, baseEnd_2890167] using wordTrace_append hprefix tailTrace_2890167
  have hstable : (prefixWord ++ tailWord_2890167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890167).length < 2 ^ (prefixWord ++ tailWord_2890167).sum := by decide
  have hdescent : baseEnd_2890167 < baseStart_2890167 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890173 : List Nat := [1, 4, 1, 2, 2, 2, 4, 2, 4]
def baseStart_2890173 : Nat := 118140960795 + 2890173 * 2 ^ 59
def prefixEnd_2890173 : Nat := 4983230072969 + 3 ^ 40 * 2890173 * 2
def baseEnd_2890173 : Nat := 329788427477116870787965

theorem tailTrace_2890173 : CollatzResearch.WordTrace tailWord_2890173 prefixEnd_2890173 329788427477116870787965 := by
  unfold tailWord_2890173
  simp only [CollatzResearch.WordTrace]
  refine ⟨105413269358404298095827173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70275512905602865397218115 105413269358404298095827173)
  ·
    refine ⟨19764988004700805892967595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105413269358404298095827173 19764988004700805892967595)
    ·
      refine ⟨29647482007051208839451393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19764988004700805892967595 29647482007051208839451393)
      ·
        refine ⟨22235611505288406629588545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29647482007051208839451393 22235611505288406629588545)
        ·
          refine ⟨16676708628966304972191409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22235611505288406629588545 16676708628966304972191409)
          ·
            refine ⟨12507531471724728729143557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16676708628966304972191409 12507531471724728729143557)
            ·
              refine ⟨2345162150948386636714417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12507531471724728729143557 2345162150948386636714417)
              ·
                refine ⟨1758871613211289977535813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2345162150948386636714417 1758871613211289977535813)
                ·
                  refine ⟨329788427477116870787965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1758871613211289977535813 329788427477116870787965)
                  ·
                    rfl

theorem cell22_2890173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_2890173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890173 prefixEnd_2890173 := by exact prefixLift 2890173
  have htrace : WordTrace (prefixWord ++ tailWord_2890173) baseStart_2890173 baseEnd_2890173 := by
    simpa [prefixWord, tailWord_2890173, baseEnd_2890173] using wordTrace_append hprefix tailTrace_2890173
  have hstable : (prefixWord ++ tailWord_2890173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890173).length < 2 ^ (prefixWord ++ tailWord_2890173).sum := by decide
  have hdescent : baseEnd_2890173 < baseStart_2890173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890184 : List Nat := [2, 1, 3, 1, 3, 2, 3, 7]
def baseStart_2890184 : Nat := 118140960795 + 2890184 * 2 ^ 59
def prefixEnd_2890184 : Nat := 4983230072969 + 3 ^ 40 * 2890184 * 2
def baseEnd_2890184 : Nat := 109929894217350027815429

theorem tailTrace_2890184 : CollatzResearch.WordTrace tailWord_2890184 prefixEnd_2890184 109929894217350027815429 := by
  unfold tailWord_2890184
  simp only [CollatzResearch.WordTrace]
  refine ⟨52706835280682223487238803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70275780374242964649651737 52706835280682223487238803)
  ·
    refine ⟨79060252921023335230858205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52706835280682223487238803 79060252921023335230858205)
    ·
      refine ⟨29647594845383750711571827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79060252921023335230858205 29647594845383750711571827)
      ·
        refine ⟨44471392268075626067357741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29647594845383750711571827 44471392268075626067357741)
        ·
          refine ⟨16676772100528359775259153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44471392268075626067357741 16676772100528359775259153)
          ·
            refine ⟨12507579075396269831444365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16676772100528359775259153 12507579075396269831444365)
            ·
              refine ⟨4690342153273601186791637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12507579075396269831444365 4690342153273601186791637)
              ·
                refine ⟨109929894217350027815429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4690342153273601186791637 109929894217350027815429)
                ·
                  rfl

theorem cell22_2890184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 7].length) (baseStart_2890184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890184 prefixEnd_2890184 := by exact prefixLift 2890184
  have htrace : WordTrace (prefixWord ++ tailWord_2890184) baseStart_2890184 baseEnd_2890184 := by
    simpa [prefixWord, tailWord_2890184, baseEnd_2890184] using wordTrace_append hprefix tailTrace_2890184
  have hstable : (prefixWord ++ tailWord_2890184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890184).length < 2 ^ (prefixWord ++ tailWord_2890184).sum := by decide
  have hdescent : baseEnd_2890184 < baseStart_2890184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890233 : List Nat := [1, 2, 1, 3, 1, 2, 4, 4, 1, 3]
def baseStart_2890233 : Nat := 118140960795 + 2890233 * 2 ^ 59
def prefixEnd_2890233 : Nat := 4983230072969 + 3 ^ 40 * 2890233 * 2
def baseEnd_2890233 : Nat := 989385821657530455863711

theorem tailTrace_2890233 : CollatzResearch.WordTrace tailWord_2890233 prefixEnd_2890233 989385821657530455863711 := by
  unfold tailWord_2890233
  simp only [CollatzResearch.WordTrace]
  refine ⟨105415457738186928343011353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70276971825457952228674235 105415457738186928343011353)
  ·
    refine ⟨79061593303640196257258515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105415457738186928343011353 79061593303640196257258515)
    ·
      refine ⟨118592389955460294385887773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79061593303640196257258515 118592389955460294385887773)
      ·
        refine ⟨44472146233297610394707915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118592389955460294385887773 44472146233297610394707915)
        ·
          refine ⟨66708219349946415592061873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44472146233297610394707915 66708219349946415592061873)
          ·
            refine ⟨50031164512459811694046405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66708219349946415592061873 50031164512459811694046405)
            ·
              refine ⟨9380843346086214692633701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50031164512459811694046405 9380843346086214692633701)
              ·
                refine ⟨1758908127391165254868819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9380843346086214692633701 1758908127391165254868819)
                ·
                  refine ⟨2638362191086747882303229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1758908127391165254868819 2638362191086747882303229)
                  ·
                    refine ⟨989385821657530455863711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638362191086747882303229 989385821657530455863711)
                    ·
                      rfl

theorem cell22_2890233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 1, 3].length) (baseStart_2890233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890233 prefixEnd_2890233 := by exact prefixLift 2890233
  have htrace : WordTrace (prefixWord ++ tailWord_2890233) baseStart_2890233 baseEnd_2890233 := by
    simpa [prefixWord, tailWord_2890233, baseEnd_2890233] using wordTrace_append hprefix tailTrace_2890233
  have hstable : (prefixWord ++ tailWord_2890233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890233).length < 2 ^ (prefixWord ++ tailWord_2890233).sum := by decide
  have hdescent : baseEnd_2890233 < baseStart_2890233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890304 : List Nat := [2, 1, 1, 2, 2, 2, 2, 1, 3, 6]
def baseStart_2890304 : Nat := 118140960795 + 2890304 * 2 ^ 59
def prefixEnd_2890304 : Nat := 4983230072969 + 3 ^ 40 * 2890304 * 2
def baseEnd_2890304 : Nat := 989410126408509937338493

theorem tailTrace_2890304 : CollatzResearch.WordTrace tailWord_2890304 prefixEnd_2890304 989410126408509937338493 := by
  unfold tailWord_2890304
  simp only [CollatzResearch.WordTrace]
  refine ⟨52709023660464853734422983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70278698213953138312563977 52709023660464853734422983)
  ·
    refine ⟨79063535490697280601634475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52709023660464853734422983 79063535490697280601634475)
    ·
      refine ⟨118595303236045920902451713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79063535490697280601634475 118595303236045920902451713)
      ·
        refine ⟨88946477427034440676838785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118595303236045920902451713 88946477427034440676838785)
        ·
          refine ⟨66709858070275830507629089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88946477427034440676838785 66709858070275830507629089)
          ·
            refine ⟨50032393552706872880721817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66709858070275830507629089 50032393552706872880721817)
            ·
              refine ⟨37524295164530154660541363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50032393552706872880721817 37524295164530154660541363)
              ·
                refine ⟨56286442746795231990812045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37524295164530154660541363 56286442746795231990812045)
                ·
                  refine ⟨21107416030048211996554517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56286442746795231990812045 21107416030048211996554517)
                  ·
                    refine ⟨989410126408509937338493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21107416030048211996554517 989410126408509937338493)
                    ·
                      rfl

theorem cell22_2890304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 3, 6].length) (baseStart_2890304 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890304 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890304 prefixEnd_2890304 := by exact prefixLift 2890304
  have htrace : WordTrace (prefixWord ++ tailWord_2890304) baseStart_2890304 baseEnd_2890304 := by
    simpa [prefixWord, tailWord_2890304, baseEnd_2890304] using wordTrace_append hprefix tailTrace_2890304
  have hstable : (prefixWord ++ tailWord_2890304).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890304).length < 2 ^ (prefixWord ++ tailWord_2890304).sum := by decide
  have hdescent : baseEnd_2890304 < baseStart_2890304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890310 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2890310 : Nat := 118140960795 + 2890310 * 2 ^ 59
def prefixEnd_2890310 : Nat := 4983230072969 + 3 ^ 40 * 2890310 * 2
def baseEnd_2890310 : Nat := 989412180331127921688475

theorem tailTrace_2890310 : CollatzResearch.WordTrace tailWord_2890310 prefixEnd_2890310 989412180331127921688475 := by
  unfold tailWord_2890310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3294320817465874077923887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70278844105938646995709589 3294320817465874077923887)
  ·
    refine ⟨4941481226198811116885831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3294320817465874077923887 4941481226198811116885831)
    ·
      refine ⟨7412221839298216675328747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4941481226198811116885831 7412221839298216675328747)
      ·
        refine ⟨11118332758947325012993121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7412221839298216675328747 11118332758947325012993121)
        ·
          refine ⟨8338749569210493759744841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11118332758947325012993121 8338749569210493759744841)
          ·
            refine ⟨6254062176907870319808631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8338749569210493759744841 6254062176907870319808631)
            ·
              refine ⟨9381093265361805479712947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6254062176907870319808631 9381093265361805479712947)
              ·
                refine ⟨14071639898042708219569421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9381093265361805479712947 14071639898042708219569421)
                ·
                  refine ⟨5276864961766015582338533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14071639898042708219569421 5276864961766015582338533)
                  ·
                    refine ⟨989412180331127921688475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5276864961766015582338533 989412180331127921688475)
                    ·
                      rfl

theorem cell22_2890310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2890310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890310 prefixEnd_2890310 := by exact prefixLift 2890310
  have htrace : WordTrace (prefixWord ++ tailWord_2890310) baseStart_2890310 baseEnd_2890310 := by
    simpa [prefixWord, tailWord_2890310, baseEnd_2890310] using wordTrace_append hprefix tailTrace_2890310
  have hstable : (prefixWord ++ tailWord_2890310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890310).length < 2 ^ (prefixWord ++ tailWord_2890310).sum := by decide
  have hdescent : baseEnd_2890310 < baseStart_2890310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890319 : List Nat := [1, 1, 2, 1, 1, 2, 6, 8]
def baseStart_2890319 : Nat := 118140960795 + 2890319 * 2 ^ 59
def prefixEnd_2890319 : Nat := 4983230072969 + 3 ^ 40 * 2890319 * 2
def baseEnd_2890319 : Nat := 109935029023894988690383

theorem tailTrace_2890319 : CollatzResearch.WordTrace tailWord_2890319 prefixEnd_2890319 109935029023894988690383 := by
  unfold tailWord_2890319
  simp only [CollatzResearch.WordTrace]
  refine ⟨105418594415875365030642011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70279062943916910020428007 105418594415875365030642011)
  ·
    refine ⟨158127891623813047545963017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105418594415875365030642011 158127891623813047545963017)
    ·
      refine ⟨118595918717859785659472263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158127891623813047545963017 118595918717859785659472263)
      ·
        refine ⟨177893878076789678489208395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118595918717859785659472263 177893878076789678489208395)
        ·
          refine ⟨266840817115184517733812593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 177893878076789678489208395 266840817115184517733812593)
          ·
            refine ⟨200130612836388388300359445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 266840817115184517733812593 200130612836388388300359445)
            ·
              refine ⟨9381122476705705701579349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 200130612836388388300359445 9381122476705705701579349)
              ·
                refine ⟨109935029023894988690383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9381122476705705701579349 109935029023894988690383)
                ·
                  rfl

theorem cell22_2890319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 8].length) (baseStart_2890319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890319 prefixEnd_2890319 := by exact prefixLift 2890319
  have htrace : WordTrace (prefixWord ++ tailWord_2890319) baseStart_2890319 baseEnd_2890319 := by
    simpa [prefixWord, tailWord_2890319, baseEnd_2890319] using wordTrace_append hprefix tailTrace_2890319
  have hstable : (prefixWord ++ tailWord_2890319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890319).length < 2 ^ (prefixWord ++ tailWord_2890319).sum := by decide
  have hdescent : baseEnd_2890319 < baseStart_2890319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890321 : List Nat := [1, 2, 2, 1, 3, 3, 1, 3, 2, 4]
def baseStart_2890321 : Nat := 118140960795 + 2890321 * 2 ^ 59
def prefixEnd_2890321 : Nat := 4983230072969 + 3 ^ 40 * 2890321 * 2
def baseEnd_2890321 : Nat := 989415945855927559663441

theorem tailTrace_2890321 : CollatzResearch.WordTrace tailWord_2890321 prefixEnd_2890321 989415945855927559663441 := by
  unfold tailWord_2890321
  simp only [CollatzResearch.WordTrace]
  refine ⟨105418667361868119372214817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70279111574578746248143211 105418667361868119372214817)
  ·
    refine ⟨79064000521401089529161113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105418667361868119372214817 79064000521401089529161113)
    ·
      refine ⟨59298000391050817146870835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79064000521401089529161113 59298000391050817146870835)
      ·
        refine ⟨88947000586576225720306253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59298000391050817146870835 88947000586576225720306253)
        ·
          refine ⟨33355125219966084645114845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 88947000586576225720306253 33355125219966084645114845)
          ·
            refine ⟨12508171957487281741918067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33355125219966084645114845 12508171957487281741918067)
            ·
              refine ⟨18762257936230922612877101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12508171957487281741918067 18762257936230922612877101)
              ·
                refine ⟨7035846726086595979828913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18762257936230922612877101 7035846726086595979828913)
                ·
                  refine ⟨5276885044564946984871685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7035846726086595979828913 5276885044564946984871685)
                  ·
                    refine ⟨989415945855927559663441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5276885044564946984871685 989415945855927559663441)
                    ·
                      rfl

theorem cell22_2890321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 3, 2, 4].length) (baseStart_2890321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890321 prefixEnd_2890321 := by exact prefixLift 2890321
  have htrace : WordTrace (prefixWord ++ tailWord_2890321) baseStart_2890321 baseEnd_2890321 := by
    simpa [prefixWord, tailWord_2890321, baseEnd_2890321] using wordTrace_append hprefix tailTrace_2890321
  have hstable : (prefixWord ++ tailWord_2890321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890321).length < 2 ^ (prefixWord ++ tailWord_2890321).sum := by decide
  have hdescent : baseEnd_2890321 < baseStart_2890321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890368 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 3, 3]
def baseStart_2890368 : Nat := 118140960795 + 2890368 * 2 ^ 59
def prefixEnd_2890368 : Nat := 4983230072969 + 3 ^ 40 * 2890368 * 2
def baseEnd_2890368 : Nat := 989432034916435103738297

theorem tailTrace_2890368 : CollatzResearch.WordTrace tailWord_2890368 prefixEnd_2890368 989432034916435103738297 := by
  unfold tailWord_2890368
  simp only [CollatzResearch.WordTrace]
  refine ⟨52710190796348923199587879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70280254395131897599450505 52710190796348923199587879)
  ·
    refine ⟨79065286194523384799381819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52710190796348923199587879 79065286194523384799381819)
    ·
      refine ⟨118597929291785077199072729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79065286194523384799381819 118597929291785077199072729)
      ·
        refine ⟨88948446968838807899304547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 118597929291785077199072729 88948446968838807899304547)
        ·
          refine ⟨133422670453258211848956821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88948446968838807899304547 133422670453258211848956821)
          ·
            refine ⟨6254187677496478680419851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 133422670453258211848956821 6254187677496478680419851)
            ·
              refine ⟨9381281516244718020629777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6254187677496478680419851 9381281516244718020629777)
              ·
                refine ⟨7035961137183538515472333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9381281516244718020629777 7035961137183538515472333)
                ·
                  refine ⟨2638485426443826943302125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7035961137183538515472333 2638485426443826943302125)
                  ·
                    refine ⟨989432034916435103738297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638485426443826943302125 989432034916435103738297)
                    ·
                      rfl

theorem cell22_2890368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 3, 3].length) (baseStart_2890368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890368 prefixEnd_2890368 := by exact prefixLift 2890368
  have htrace : WordTrace (prefixWord ++ tailWord_2890368) baseStart_2890368 baseEnd_2890368 := by
    simpa [prefixWord, tailWord_2890368, baseEnd_2890368] using wordTrace_append hprefix tailTrace_2890368
  have hstable : (prefixWord ++ tailWord_2890368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890368).length < 2 ^ (prefixWord ++ tailWord_2890368).sum := by decide
  have hdescent : baseEnd_2890368 < baseStart_2890368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890398 : List Nat := [4, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_2890398 : Nat := 118140960795 + 2890398 * 2 ^ 59
def prefixEnd_2890398 : Nat := 4983230072969 + 3 ^ 40 * 2890398 * 2
def baseEnd_2890398 : Nat := 329814101509841675162735

theorem tailTrace_2890398 : CollatzResearch.WordTrace tailWord_2890398 prefixEnd_2890398 329814101509841675162735 := by
  unfold tailWord_2890398
  simp only [CollatzResearch.WordTrace]
  refine ⟨13177684472823645190345981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70280983855059441015178565 13177684472823645190345981)
  ·
    refine ⟨4941631677308866946379743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13177684472823645190345981 4941631677308866946379743)
    ·
      refine ⟨7412447515963300419569615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4941631677308866946379743 7412447515963300419569615)
      ·
        refine ⟨11118671273944950629354423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7412447515963300419569615 11118671273944950629354423)
        ·
          refine ⟨16678006910917425944031635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11118671273944950629354423 16678006910917425944031635)
          ·
            refine ⟨25017010366376138916047453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16678006910917425944031635 25017010366376138916047453)
            ·
              refine ⟨9381378887391052093517795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25017010366376138916047453 9381378887391052093517795)
              ·
                refine ⟨14072068331086578140276693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9381378887391052093517795 14072068331086578140276693)
                ·
                  refine ⟨329814101509841675162735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14072068331086578140276693 329814101509841675162735)
                  ·
                    rfl

theorem cell22_2890398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_2890398 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890398 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890398 prefixEnd_2890398 := by exact prefixLift 2890398
  have htrace : WordTrace (prefixWord ++ tailWord_2890398) baseStart_2890398 baseEnd_2890398 := by
    simpa [prefixWord, tailWord_2890398, baseEnd_2890398] using wordTrace_append hprefix tailTrace_2890398
  have hstable : (prefixWord ++ tailWord_2890398).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890398).length < 2 ^ (prefixWord ++ tailWord_2890398).sum := by decide
  have hdescent : baseEnd_2890398 < baseStart_2890398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890413 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 2, 5]
def baseStart_2890413 : Nat := 118140960795 + 2890413 * 2 ^ 59
def prefixEnd_2890413 : Nat := 4983230072969 + 3 ^ 40 * 2890413 * 2
def baseEnd_2890413 : Nat := 989447439336069986363159

theorem tailTrace_2890413 : CollatzResearch.WordTrace tailWord_2890413 prefixEnd_2890413 989447439336069986363159 := by
  unfold tailWord_2890413
  simp only [CollatzResearch.WordTrace]
  refine ⟨105422022877534819084563893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70281348585023212723042595 105422022877534819084563893)
  ·
    refine ⟨9883314644768889289177865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105422022877534819084563893 9883314644768889289177865)
    ·
      refine ⟨7412485983576666966883399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9883314644768889289177865 7412485983576666966883399)
      ·
        refine ⟨11118728975365000450325099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7412485983576666966883399 11118728975365000450325099)
        ·
          refine ⟨16678093463047500675487649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11118728975365000450325099 16678093463047500675487649)
          ·
            refine ⟨12508570097285625506615737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16678093463047500675487649 12508570097285625506615737)
            ·
              refine ⟨9381427572964219129961803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12508570097285625506615737 9381427572964219129961803)
              ·
                refine ⟨14072141359446328694942705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9381427572964219129961803 14072141359446328694942705)
                ·
                  refine ⟨10554106019584746521207029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14072141359446328694942705 10554106019584746521207029)
                  ·
                    refine ⟨989447439336069986363159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10554106019584746521207029 989447439336069986363159)
                    ·
                      rfl

theorem cell22_2890413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_2890413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890413 prefixEnd_2890413 := by exact prefixLift 2890413
  have htrace : WordTrace (prefixWord ++ tailWord_2890413) baseStart_2890413 baseEnd_2890413 := by
    simpa [prefixWord, tailWord_2890413, baseEnd_2890413] using wordTrace_append hprefix tailTrace_2890413
  have hstable : (prefixWord ++ tailWord_2890413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890413).length < 2 ^ (prefixWord ++ tailWord_2890413).sum := by decide
  have hdescent : baseEnd_2890413 < baseStart_2890413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890426 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 6]
def baseStart_2890426 : Nat := 118140960795 + 2890426 * 2 ^ 59
def prefixEnd_2890426 : Nat := 4983230072969 + 3 ^ 40 * 2890426 * 2
def baseEnd_2890426 : Nat := 329817296500580761929373

theorem tailTrace_2890426 : CollatzResearch.WordTrace tailWord_2890426 prefixEnd_2890426 329817296500580761929373 := by
  unfold tailWord_2890426
  simp only [CollatzResearch.WordTrace]
  refine ⟨26355624256621930576196783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70281664684325148203191421 26355624256621930576196783)
  ·
    refine ⟨39533436384932895864295175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26355624256621930576196783 39533436384932895864295175)
    ·
      refine ⟨59300154577399343796442763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39533436384932895864295175 59300154577399343796442763)
      ·
        refine ⟨88950231866099015694664145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59300154577399343796442763 88950231866099015694664145)
        ·
          refine ⟨66712673899574261770998109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88950231866099015694664145 66712673899574261770998109)
          ·
            refine ⟨25017252712340348164124291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 66712673899574261770998109 25017252712340348164124291)
            ·
              refine ⟨37525879068510522246186437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25017252712340348164124291 37525879068510522246186437)
              ·
                refine ⟨7036102325345722921159957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37525879068510522246186437 7036102325345722921159957)
                ·
                  refine ⟨329817296500580761929373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7036102325345722921159957 329817296500580761929373)
                  ·
                    rfl

theorem cell22_2890426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 6].length) (baseStart_2890426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890426 prefixEnd_2890426 := by exact prefixLift 2890426
  have htrace : WordTrace (prefixWord ++ tailWord_2890426) baseStart_2890426 baseEnd_2890426 := by
    simpa [prefixWord, tailWord_2890426, baseEnd_2890426] using wordTrace_append hprefix tailTrace_2890426
  have hstable : (prefixWord ++ tailWord_2890426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890426).length < 2 ^ (prefixWord ++ tailWord_2890426).sum := by decide
  have hdescent : baseEnd_2890426 < baseStart_2890426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890458 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 4, 3]
def baseStart_2890458 : Nat := 118140960795 + 2890458 * 2 ^ 59
def prefixEnd_2890458 : Nat := 4983230072969 + 3 ^ 40 * 2890458 * 2
def baseEnd_2890458 : Nat := 989462843755704868988021

theorem tailTrace_2890458 : CollatzResearch.WordTrace tailWord_2890458 prefixEnd_2890458 989462843755704868988021 := by
  unfold tailWord_2890458
  simp only [CollatzResearch.WordTrace]
  refine ⟨26355916040592947942488007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70282442774914527846634685 26355916040592947942488007)
  ·
    refine ⟨39533874060889421913732011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26355916040592947942488007 39533874060889421913732011)
    ·
      refine ⟨59300811091334132870598017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39533874060889421913732011 59300811091334132870598017)
      ·
        refine ⟨44475608318500599652948513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59300811091334132870598017 44475608318500599652948513)
        ·
          refine ⟨33356706238875449739711385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44475608318500599652948513 33356706238875449739711385)
          ·
            refine ⟨25017529679156587304783539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33356706238875449739711385 25017529679156587304783539)
            ·
              refine ⟨37526294518734880957175309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25017529679156587304783539 37526294518734880957175309)
              ·
                refine ⟨14072360444525580358940741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37526294518734880957175309 14072360444525580358940741)
                ·
                  refine ⟨2638567583348546317301389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14072360444525580358940741 2638567583348546317301389)
                  ·
                    refine ⟨989462843755704868988021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638567583348546317301389 989462843755704868988021)
                    ·
                      rfl

theorem cell22_2890458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 4, 3].length) (baseStart_2890458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890458 prefixEnd_2890458 := by exact prefixLift 2890458
  have htrace : WordTrace (prefixWord ++ tailWord_2890458) baseStart_2890458 baseEnd_2890458 := by
    simpa [prefixWord, tailWord_2890458, baseEnd_2890458] using wordTrace_append hprefix tailTrace_2890458
  have hstable : (prefixWord ++ tailWord_2890458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890458).length < 2 ^ (prefixWord ++ tailWord_2890458).sum := by decide
  have hdescent : baseEnd_2890458 < baseStart_2890458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890460 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 6]
def baseStart_2890460 : Nat := 118140960795 + 2890460 * 2 ^ 59
def prefixEnd_2890460 : Nat := 4983230072969 + 3 ^ 40 * 2890460 * 2
def baseEnd_2890460 : Nat := 329821176132192510146005

theorem tailTrace_2890460 : CollatzResearch.WordTrace tailWord_2890460 prefixEnd_2890460 329821176132192510146005 := by
  unfold tailWord_2890460
  simp only [CollatzResearch.WordTrace]
  refine ⟨52711868554182273055762417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70282491405576364074349889 52711868554182273055762417)
  ·
    refine ⟨39533901415636704791821813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52711868554182273055762417 39533901415636704791821813)
    ·
      refine ⟨3706303257715941074233295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39533901415636704791821813 3706303257715941074233295)
      ·
        refine ⟨5559454886573911611349943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3706303257715941074233295 5559454886573911611349943)
        ·
          refine ⟨8339182329860867417024915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5559454886573911611349943 8339182329860867417024915)
          ·
            refine ⟨12508773494791301125537373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8339182329860867417024915 12508773494791301125537373)
            ·
              refine ⟨4690790060546737922076515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12508773494791301125537373 4690790060546737922076515)
              ·
                refine ⟨7036185090820106883114773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4690790060546737922076515 7036185090820106883114773)
                ·
                  refine ⟨329821176132192510146005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7036185090820106883114773 329821176132192510146005)
                  ·
                    rfl

theorem cell22_2890460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_2890460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890460 prefixEnd_2890460 := by exact prefixLift 2890460
  have htrace : WordTrace (prefixWord ++ tailWord_2890460) baseStart_2890460 baseEnd_2890460 := by
    simpa [prefixWord, tailWord_2890460, baseEnd_2890460] using wordTrace_append hprefix tailTrace_2890460
  have hstable : (prefixWord ++ tailWord_2890460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890460).length < 2 ^ (prefixWord ++ tailWord_2890460).sum := by decide
  have hdescent : baseEnd_2890460 < baseStart_2890460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890501 : List Nat := [1, 3, 1, 1, 2, 1, 1, 2, 4, 6]
def baseStart_2890501 : Nat := 118140960795 + 2890501 * 2 ^ 59
def prefixEnd_2890501 : Nat := 4983230072969 + 3 ^ 40 * 2890501 * 2
def baseEnd_2890501 : Nat := 989477563534467090162889

theorem tailTrace_2890501 : CollatzResearch.WordTrace tailWord_2890501 prefixEnd_2890501 989477563534467090162889 := by
  unfold tailWord_2890501
  simp only [CollatzResearch.WordTrace]
  refine ⟨105425232501216010113767357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70283488334144006742511571 105425232501216010113767357)
  ·
    refine ⟨39534462187956003792662759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105425232501216010113767357 39534462187956003792662759)
    ·
      refine ⟨59301693281934005688994139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39534462187956003792662759 59301693281934005688994139)
      ·
        refine ⟨88952539922901008533491209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59301693281934005688994139 88952539922901008533491209)
        ·
          refine ⟨66714404942175756400118407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88952539922901008533491209 66714404942175756400118407)
          ·
            refine ⟨100071607413263634600177611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66714404942175756400118407 100071607413263634600177611)
            ·
              refine ⟨150107411119895451900266417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100071607413263634600177611 150107411119895451900266417)
              ·
                refine ⟨112580558339921588925199813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150107411119895451900266417 112580558339921588925199813)
                ·
                  refine ⟨21108854688735297923474965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 112580558339921588925199813 21108854688735297923474965)
                  ·
                    refine ⟨989477563534467090162889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21108854688735297923474965 989477563534467090162889)
                    ·
                      rfl

theorem cell22_2890501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_2890501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890501 prefixEnd_2890501 := by exact prefixLift 2890501
  have htrace : WordTrace (prefixWord ++ tailWord_2890501) baseStart_2890501 baseEnd_2890501 := by
    simpa [prefixWord, tailWord_2890501, baseEnd_2890501] using wordTrace_append hprefix tailTrace_2890501
  have hstable : (prefixWord ++ tailWord_2890501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890501).length < 2 ^ (prefixWord ++ tailWord_2890501).sum := by decide
  have hdescent : baseEnd_2890501 < baseStart_2890501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890533 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 5]
def baseStart_2890533 : Nat := 118140960795 + 2890533 * 2 ^ 59
def prefixEnd_2890533 : Nat := 4983230072969 + 3 ^ 40 * 2890533 * 2
def baseEnd_2890533 : Nat := 329829505929476557787597

theorem tailTrace_2890533 : CollatzResearch.WordTrace tailWord_2890533 prefixEnd_2890533 329829505929476557787597 := by
  unfold tailWord_2890533
  simp only [CollatzResearch.WordTrace]
  refine ⟨105426399637100079578932253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70284266424733386385954835 105426399637100079578932253)
  ·
    refine ⟨39534899863912529842099595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105426399637100079578932253 39534899863912529842099595)
    ·
      refine ⟨59302349795868794763149393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39534899863912529842099595 59302349795868794763149393)
      ·
        refine ⟨44476762346901596072362045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59302349795868794763149393 44476762346901596072362045)
        ·
          refine ⟨16678785880088098527135767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44476762346901596072362045 16678785880088098527135767)
          ·
            refine ⟨25018178820132147790703651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16678785880088098527135767 25018178820132147790703651)
            ·
              refine ⟨37527268230198221686055477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25018178820132147790703651 37527268230198221686055477)
              ·
                refine ⟨3518181396581083283067701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37527268230198221686055477 3518181396581083283067701)
                ·
                  refine ⟨329829505929476557787597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3518181396581083283067701 329829505929476557787597)
                  ·
                    rfl

theorem cell22_2890533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 5].length) (baseStart_2890533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890533 prefixEnd_2890533 := by exact prefixLift 2890533
  have htrace : WordTrace (prefixWord ++ tailWord_2890533) baseStart_2890533 baseEnd_2890533 := by
    simpa [prefixWord, tailWord_2890533, baseEnd_2890533] using wordTrace_append hprefix tailTrace_2890533
  have hstable : (prefixWord ++ tailWord_2890533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890533).length < 2 ^ (prefixWord ++ tailWord_2890533).sum := by decide
  have hdescent : baseEnd_2890533 < baseStart_2890533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890541 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2890541 : Nat := 118140960795 + 2890541 * 2 ^ 59
def prefixEnd_2890541 : Nat := 4983230072969 + 3 ^ 40 * 2890541 * 2
def baseEnd_2890541 : Nat := 989491256351920319162767

theorem tailTrace_2890541 : CollatzResearch.WordTrace tailWord_2890541 prefixEnd_2890541 989491256351920319162767 := by
  unfold tailWord_2890541
  simp only [CollatzResearch.WordTrace]
  refine ⟨105426691421071096945223477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70284460947380731296815651 105426691421071096945223477)
  ·
    refine ⟨9883752320725415338614701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 105426691421071096945223477 9883752320725415338614701)
    ·
      refine ⟨3706407120272030751980513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9883752320725415338614701 3706407120272030751980513)
      ·
        refine ⟨2779805340204023063985385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3706407120272030751980513 2779805340204023063985385)
        ·
          refine ⟨2084854005153017297989039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2779805340204023063985385 2084854005153017297989039)
          ·
            refine ⟨3127281007729525946983559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2084854005153017297989039 3127281007729525946983559)
            ·
              refine ⟨4690921511594288920475339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127281007729525946983559 4690921511594288920475339)
              ·
                refine ⟨7036382267391433380713009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4690921511594288920475339 7036382267391433380713009)
                ·
                  refine ⟨5277286700543575035534757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7036382267391433380713009 5277286700543575035534757)
                  ·
                    refine ⟨989491256351920319162767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5277286700543575035534757 989491256351920319162767)
                    ·
                      rfl

theorem cell22_2890541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2890541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890541 prefixEnd_2890541 := by exact prefixLift 2890541
  have htrace : WordTrace (prefixWord ++ tailWord_2890541) baseStart_2890541 baseEnd_2890541 := by
    simpa [prefixWord, tailWord_2890541, baseEnd_2890541] using wordTrace_append hprefix tailTrace_2890541
  have hstable : (prefixWord ++ tailWord_2890541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890541).length < 2 ^ (prefixWord ++ tailWord_2890541).sum := by decide
  have hdescent : baseEnd_2890541 < baseStart_2890541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890554 : List Nat := [3, 1, 1, 1, 6, 1, 2, 3, 1, 3]
def baseStart_2890554 : Nat := 118140960795 + 2890554 * 2 ^ 59
def prefixEnd_2890554 : Nat := 4983230072969 + 3 ^ 40 * 2890554 * 2
def baseEnd_2890554 : Nat := 989495706517592618587727

theorem tailTrace_2890554 : CollatzResearch.WordTrace tailWord_2890554 prefixEnd_2890554 989495706517592618587727 := by
  unfold tailWord_2890554
  simp only [CollatzResearch.WordTrace]
  refine ⟨26356791392506000041361679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70284777046682666776964477 26356791392506000041361679)
  ·
    refine ⟨39535187088759000062042519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26356791392506000041361679 39535187088759000062042519)
    ·
      refine ⟨59302780633138500093063779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39535187088759000062042519 59302780633138500093063779)
      ·
        refine ⟨88954170949707750139595669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59302780633138500093063779 88954170949707750139595669)
        ·
          refine ⟨4169726763267550787793547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 88954170949707750139595669 4169726763267550787793547)
          ·
            refine ⟨6254590144901326181690321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4169726763267550787793547 6254590144901326181690321)
            ·
              refine ⟨4690942608675994636267741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6254590144901326181690321 4690942608675994636267741)
              ·
                refine ⟨1759103478253497988600403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4690942608675994636267741 1759103478253497988600403)
                ·
                  refine ⟨2638655217380246982900605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759103478253497988600403 2638655217380246982900605)
                  ·
                    refine ⟨989495706517592618587727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638655217380246982900605 989495706517592618587727)
                    ·
                      rfl

theorem cell22_2890554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 1, 3].length) (baseStart_2890554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890554 prefixEnd_2890554 := by exact prefixLift 2890554
  have htrace : WordTrace (prefixWord ++ tailWord_2890554) baseStart_2890554 baseEnd_2890554 := by
    simpa [prefixWord, tailWord_2890554, baseEnd_2890554] using wordTrace_append hprefix tailTrace_2890554
  have hstable : (prefixWord ++ tailWord_2890554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890554).length < 2 ^ (prefixWord ++ tailWord_2890554).sum := by decide
  have hdescent : baseEnd_2890554 < baseStart_2890554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890593 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 1, 5]
def baseStart_2890593 : Nat := 118140960795 + 2890593 * 2 ^ 59
def prefixEnd_2890593 : Nat := 4983230072969 + 3 ^ 40 * 2890593 * 2
def baseEnd_2890593 : Nat := 989509057014609516862607

theorem tailTrace_2890593 : CollatzResearch.WordTrace tailWord_2890593 prefixEnd_2890593 989509057014609516862607 := by
  unfold tailWord_2890593
  simp only [CollatzResearch.WordTrace]
  refine ⟨105428588016882709826116433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70285725344588473217410955 105428588016882709826116433)
  ·
    refine ⟨79071441012662032369587325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105428588016882709826116433 79071441012662032369587325)
    ·
      refine ⟨29651790379748262138595247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79071441012662032369587325 29651790379748262138595247)
      ·
        refine ⟨44477685569622393207892871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29651790379748262138595247 44477685569622393207892871)
        ·
          refine ⟨66716528354433589811839307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44477685569622393207892871 66716528354433589811839307)
          ·
            refine ⟨100074792531650384717758961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66716528354433589811839307 100074792531650384717758961)
            ·
              refine ⟨75056094398737788538319221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100074792531650384717758961 75056094398737788538319221)
              ·
                refine ⟨7036508849881667675467427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75056094398737788538319221 7036508849881667675467427)
                ·
                  refine ⟨10554763274822501513201141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7036508849881667675467427 10554763274822501513201141)
                  ·
                    refine ⟨989509057014609516862607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10554763274822501513201141 989509057014609516862607)
                    ·
                      rfl

theorem cell22_2890593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 1, 5].length) (baseStart_2890593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890593 prefixEnd_2890593 := by exact prefixLift 2890593
  have htrace : WordTrace (prefixWord ++ tailWord_2890593) baseStart_2890593 baseEnd_2890593 := by
    simpa [prefixWord, tailWord_2890593, baseEnd_2890593] using wordTrace_append hprefix tailTrace_2890593
  have hstable : (prefixWord ++ tailWord_2890593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890593).length < 2 ^ (prefixWord ++ tailWord_2890593).sum := by decide
  have hdescent : baseEnd_2890593 < baseStart_2890593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890608 : List Nat := [2, 1, 1, 1, 4, 1, 4, 1, 1, 6]
def baseStart_2890608 : Nat := 118140960795 + 2890608 * 2 ^ 59
def prefixEnd_2890608 : Nat := 4983230072969 + 3 ^ 40 * 2890608 * 2
def baseEnd_2890608 : Nat := 989514191821154477737561

theorem tailTrace_2890608 : CollatzResearch.WordTrace tailWord_2890608 prefixEnd_2890608 989514191821154477737561 := by
  unfold tailWord_2890608
  simp only [CollatzResearch.WordTrace]
  refine ⟨52714567555914183693956239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70286090074552244925274985 52714567555914183693956239)
  ·
    refine ⟨79071851333871275540934359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52714567555914183693956239 79071851333871275540934359)
    ·
      refine ⟨118607777000806913311401539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79071851333871275540934359 118607777000806913311401539)
      ·
        refine ⟨177911665501210369967102309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118607777000806913311401539 177911665501210369967102309)
        ·
          refine ⟨33358437281476944368831683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 177911665501210369967102309 33358437281476944368831683)
          ·
            refine ⟨50037655922215416553247525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33358437281476944368831683 50037655922215416553247525)
            ·
              refine ⟨9382060485415390603733911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50037655922215416553247525 9382060485415390603733911)
              ·
                refine ⟨14073090728123085905600867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9382060485415390603733911 14073090728123085905600867)
                ·
                  refine ⟨21109636092184628858401301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14073090728123085905600867 21109636092184628858401301)
                  ·
                    refine ⟨989514191821154477737561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21109636092184628858401301 989514191821154477737561)
                    ·
                      rfl

theorem cell22_2890608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 4, 1, 1, 6].length) (baseStart_2890608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890608 prefixEnd_2890608 := by exact prefixLift 2890608
  have htrace : WordTrace (prefixWord ++ tailWord_2890608) baseStart_2890608 baseEnd_2890608 := by
    simpa [prefixWord, tailWord_2890608, baseEnd_2890608] using wordTrace_append hprefix tailTrace_2890608
  have hstable : (prefixWord ++ tailWord_2890608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890608).length < 2 ^ (prefixWord ++ tailWord_2890608).sum := by decide
  have hdescent : baseEnd_2890608 < baseStart_2890608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890610 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 4, 3]
def baseStart_2890610 : Nat := 118140960795 + 2890610 * 2 ^ 59
def prefixEnd_2890610 : Nat := 4983230072969 + 3 ^ 40 * 2890610 * 2
def baseEnd_2890610 : Nat := 989514876462027139187555

theorem tailTrace_2890610 : CollatzResearch.WordTrace tailWord_2890610 prefixEnd_2890610 989514876462027139187555 := by
  unfold tailWord_2890610
  simp only [CollatzResearch.WordTrace]
  refine ⟨26357302014455280432371321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70286138705214081152990189 26357302014455280432371321)
  ·
    refine ⟨19767976510841460324278491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26357302014455280432371321 19767976510841460324278491)
    ·
      refine ⟨29651964766262190486417737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19767976510841460324278491 29651964766262190486417737)
      ·
        refine ⟨22238973574696642864813303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29651964766262190486417737 22238973574696642864813303)
        ·
          refine ⟨33358460362044964297219955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22238973574696642864813303 33358460362044964297219955)
          ·
            refine ⟨50037690543067446445829933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33358460362044964297219955 50037690543067446445829933)
            ·
              refine ⟨18764133953650292417186225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50037690543067446445829933 18764133953650292417186225)
              ·
                refine ⟨14073100465237719312889669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18764133953650292417186225 14073100465237719312889669)
                ·
                  refine ⟨2638706337232072371166813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14073100465237719312889669 2638706337232072371166813)
                  ·
                    refine ⟨989514876462027139187555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638706337232072371166813 989514876462027139187555)
                    ·
                      rfl

theorem cell22_2890610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 4, 3].length) (baseStart_2890610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890610 prefixEnd_2890610 := by exact prefixLift 2890610
  have htrace : WordTrace (prefixWord ++ tailWord_2890610) baseStart_2890610 baseEnd_2890610 := by
    simpa [prefixWord, tailWord_2890610, baseEnd_2890610] using wordTrace_append hprefix tailTrace_2890610
  have hstable : (prefixWord ++ tailWord_2890610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890610).length < 2 ^ (prefixWord ++ tailWord_2890610).sum := by decide
  have hdescent : baseEnd_2890610 < baseStart_2890610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890700 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 2, 5]
def baseStart_2890700 : Nat := 118140960795 + 2890700 * 2 ^ 59
def prefixEnd_2890700 : Nat := 4983230072969 + 3 ^ 40 * 2890700 * 2
def baseEnd_2890700 : Nat := 989545685301296904437279

theorem tailTrace_2890700 : CollatzResearch.WordTrace tailWord_2890700 prefixEnd_2890700 989545685301296904437279 := by
  unfold tailWord_2890700
  simp only [CollatzResearch.WordTrace]
  refine ⟨52716245313747533550130777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70288327084996711400174369 52716245313747533550130777)
  ·
    refine ⟨39537183985310650162598083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52716245313747533550130777 39537183985310650162598083)
    ·
      refine ⟨59305775977965975243897125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39537183985310650162598083 59305775977965975243897125)
      ·
        refine ⟨11119832995868620358230711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59305775977965975243897125 11119832995868620358230711)
        ·
          refine ⟨16679749493802930537346067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11119832995868620358230711 16679749493802930537346067)
          ·
            refine ⟨25019624240704395806019101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16679749493802930537346067 25019624240704395806019101)
            ·
              refine ⟨9382359090264148427257163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25019624240704395806019101 9382359090264148427257163)
              ·
                refine ⟨14073538635396222640885745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9382359090264148427257163 14073538635396222640885745)
                ·
                  refine ⟨10555153976547166980664309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14073538635396222640885745 10555153976547166980664309)
                  ·
                    refine ⟨989545685301296904437279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10555153976547166980664309 989545685301296904437279)
                    ·
                      rfl

theorem cell22_2890700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_2890700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890700 prefixEnd_2890700 := by exact prefixLift 2890700
  have htrace : WordTrace (prefixWord ++ tailWord_2890700) baseStart_2890700 baseEnd_2890700 := by
    simpa [prefixWord, tailWord_2890700, baseEnd_2890700] using wordTrace_append hprefix tailTrace_2890700
  have hstable : (prefixWord ++ tailWord_2890700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890700).length < 2 ^ (prefixWord ++ tailWord_2890700).sum := by decide
  have hdescent : baseEnd_2890700 < baseStart_2890700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890740 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 3, 3]
def baseStart_2890740 : Nat := 118140960795 + 2890740 * 2 ^ 59
def prefixEnd_2890740 : Nat := 4983230072969 + 3 ^ 40 * 2890740 * 2
def baseEnd_2890740 : Nat := 989559378118750133437157

theorem tailTrace_2890740 : CollatzResearch.WordTrace tailWord_2890740 prefixEnd_2890740 989559378118750133437157 := by
  unfold tailWord_2890740
  simp only [CollatzResearch.WordTrace]
  refine ⟨52716974773675076965858837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70289299698233435954478449 52716974773675076965858837)
  ·
    refine ⟨2471108192516019232774633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 52716974773675076965858837 2471108192516019232774633)
    ·
      refine ⟨1853331144387014424580975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2471108192516019232774633 1853331144387014424580975)
      ·
        refine ⟨2779996716580521636871463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853331144387014424580975 2779996716580521636871463)
        ·
          refine ⟨4169995074870782455307195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2779996716580521636871463 4169995074870782455307195)
          ·
            refine ⟨6254992612306173682960793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4169995074870782455307195 6254992612306173682960793)
            ·
              refine ⟨4691244459229630262220595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6254992612306173682960793 4691244459229630262220595)
              ·
                refine ⟨7036866688844445393330893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691244459229630262220595 7036866688844445393330893)
                ·
                  refine ⟨2638825008316667022499085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7036866688844445393330893 2638825008316667022499085)
                  ·
                    refine ⟨989559378118750133437157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638825008316667022499085 989559378118750133437157)
                    ·
                      rfl

theorem cell22_2890740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_2890740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890740 prefixEnd_2890740 := by exact prefixLift 2890740
  have htrace : WordTrace (prefixWord ++ tailWord_2890740) baseStart_2890740 baseEnd_2890740 := by
    simpa [prefixWord, tailWord_2890740, baseEnd_2890740] using wordTrace_append hprefix tailTrace_2890740
  have hstable : (prefixWord ++ tailWord_2890740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890740).length < 2 ^ (prefixWord ++ tailWord_2890740).sum := by decide
  have hdescent : baseEnd_2890740 < baseStart_2890740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890760 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 1, 6]
def baseStart_2890760 : Nat := 118140960795 + 2890760 * 2 ^ 59
def prefixEnd_2890760 : Nat := 4983230072969 + 3 ^ 40 * 2890760 * 2
def baseEnd_2890760 : Nat := 989566224527476747937095

theorem tailTrace_2890760 : CollatzResearch.WordTrace tailWord_2890760 prefixEnd_2890760 989566224527476747937095 := by
  unfold tailWord_2890760
  simp only [CollatzResearch.WordTrace]
  refine ⟨52717339503638848673722867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70289786004851798231630489 52717339503638848673722867)
  ·
    refine ⟨79076009255458273010584301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52717339503638848673722867 79076009255458273010584301)
    ·
      refine ⟨29653503470796852378969113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79076009255458273010584301 29653503470796852378969113)
      ·
        refine ⟨22240127603097639284226835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29653503470796852378969113 22240127603097639284226835)
        ·
          refine ⟨33360191404646458926340253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22240127603097639284226835 33360191404646458926340253)
          ·
            refine ⟨12510071776742422097377595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33360191404646458926340253 12510071776742422097377595)
            ·
              refine ⟨18765107665113633146066393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12510071776742422097377595 18765107665113633146066393)
              ·
                refine ⟨14073830748835224859549795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18765107665113633146066393 14073830748835224859549795)
                ·
                  refine ⟨21110746123252837289324693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14073830748835224859549795 21110746123252837289324693)
                  ·
                    refine ⟨989566224527476747937095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21110746123252837289324693 989566224527476747937095)
                    ·
                      rfl

theorem cell22_2890760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_2890760 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890760 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890760 prefixEnd_2890760 := by exact prefixLift 2890760
  have htrace : WordTrace (prefixWord ++ tailWord_2890760) baseStart_2890760 baseEnd_2890760 := by
    simpa [prefixWord, tailWord_2890760, baseEnd_2890760] using wordTrace_append hprefix tailTrace_2890760
  have hstable : (prefixWord ++ tailWord_2890760).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890760).length < 2 ^ (prefixWord ++ tailWord_2890760).sum := by decide
  have hdescent : baseEnd_2890760 < baseStart_2890760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890762 : List Nat := [3, 1, 2, 2, 3, 1, 3, 1, 1, 5]
def baseStart_2890762 : Nat := 118140960795 + 2890762 * 2 ^ 59
def prefixEnd_2890762 : Nat := 4983230072969 + 3 ^ 40 * 2890762 * 2
def baseEnd_2890762 : Nat := 989566909168349409387089

theorem tailTrace_2890762 : CollatzResearch.WordTrace tailWord_2890762 prefixEnd_2890762 989566909168349409387089 := by
  unfold tailWord_2890762
  simp only [CollatzResearch.WordTrace]
  refine ⟨26358687988317612922254635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70289834635513634459345693 26358687988317612922254635)
  ·
    refine ⟨39538031982476419383381953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26358687988317612922254635 39538031982476419383381953)
    ·
      refine ⟨29653523986857314537536465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39538031982476419383381953 29653523986857314537536465)
      ·
        refine ⟨22240142990142985903152349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29653523986857314537536465 22240142990142985903152349)
        ·
          refine ⟨8340053621303619713682131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22240142990142985903152349 8340053621303619713682131)
          ·
            refine ⟨12510080431955429570523197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8340053621303619713682131 12510080431955429570523197)
            ·
              refine ⟨4691280161983286088946199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12510080431955429570523197 4691280161983286088946199)
              ·
                refine ⟨7036920242974929133419299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691280161983286088946199 7036920242974929133419299)
                ·
                  refine ⟨10555380364462393700128949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7036920242974929133419299 10555380364462393700128949)
                  ·
                    refine ⟨989566909168349409387089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10555380364462393700128949 989566909168349409387089)
                    ·
                      rfl

theorem cell22_2890762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_2890762 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890762 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890762 prefixEnd_2890762 := by exact prefixLift 2890762
  have htrace : WordTrace (prefixWord ++ tailWord_2890762) baseStart_2890762 baseEnd_2890762 := by
    simpa [prefixWord, tailWord_2890762, baseEnd_2890762] using wordTrace_append hprefix tailTrace_2890762
  have hstable : (prefixWord ++ tailWord_2890762).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890762).length < 2 ^ (prefixWord ++ tailWord_2890762).sum := by decide
  have hdescent : baseEnd_2890762 < baseStart_2890762 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890781 : List Nat := [1, 4, 2, 2, 3, 2, 1, 3, 4]
def baseStart_2890781 : Nat := 118140960795 + 2890781 * 2 ^ 59
def prefixEnd_2890781 : Nat := 4983230072969 + 3 ^ 40 * 2890781 * 2
def baseEnd_2890781 : Nat := 329857804418879897720677

theorem tailTrace_2890781 : CollatzResearch.WordTrace tailWord_2890781 prefixEnd_2890781 329857804418879897720677 := by
  unfold tailWord_2890781
  simp only [CollatzResearch.WordTrace]
  refine ⟨105435444940201617933960197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70290296626801078622640131 105435444940201617933960197)
  ·
    refine ⟨19769145926287803362617537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 105435444940201617933960197 19769145926287803362617537)
    ·
      refine ⟨14826859444715852521963153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19769145926287803362617537 14826859444715852521963153)
      ·
        refine ⟨11120144583536889391472365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14826859444715852521963153 11120144583536889391472365)
        ·
          refine ⟨4170054218826333521802137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11120144583536889391472365 4170054218826333521802137)
          ·
            refine ⟨3127540664119750141351603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4170054218826333521802137 3127540664119750141351603)
            ·
              refine ⟨4691310996179625212027405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127540664119750141351603 4691310996179625212027405)
              ·
                refine ⟨1759241623567359454510277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4691310996179625212027405 1759241623567359454510277)
                ·
                  refine ⟨329857804418879897720677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1759241623567359454510277 329857804418879897720677)
                  ·
                    rfl

theorem cell22_2890781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_2890781 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890781 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890781 prefixEnd_2890781 := by exact prefixLift 2890781
  have htrace : WordTrace (prefixWord ++ tailWord_2890781) baseStart_2890781 baseEnd_2890781 := by
    simpa [prefixWord, tailWord_2890781, baseEnd_2890781] using wordTrace_append hprefix tailTrace_2890781
  have hstable : (prefixWord ++ tailWord_2890781).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890781).length < 2 ^ (prefixWord ++ tailWord_2890781).sum := by decide
  have hdescent : baseEnd_2890781 < baseStart_2890781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890794 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 2, 4]
def baseStart_2890794 : Nat := 118140960795 + 2890794 * 2 ^ 59
def prefixEnd_2890794 : Nat := 4983230072969 + 3 ^ 40 * 2890794 * 2
def baseEnd_2890794 : Nat := 989577863422311992586991

theorem tailTrace_2890794 : CollatzResearch.WordTrace tailWord_2890794 prefixEnd_2890794 989577863422311992586991 := by
  unfold tailWord_2890794
  simp only [CollatzResearch.WordTrace]
  refine ⟨26358979772288630288545859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70290612726103014102788957 26358979772288630288545859)
  ·
    refine ⟨39538469658432945432818789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26358979772288630288545859 39538469658432945432818789)
    ·
      refine ⟨7413463060956177268653523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39538469658432945432818789 7413463060956177268653523)
      ·
        refine ⟨11120194591434265902980285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7413463060956177268653523 11120194591434265902980285)
        ·
          refine ⟨4170072971787849713617607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11120194591434265902980285 4170072971787849713617607)
          ·
            refine ⟨6255109457681774570426411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4170072971787849713617607 6255109457681774570426411)
            ·
              refine ⟨9382664186522661855639617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6255109457681774570426411 9382664186522661855639617)
              ·
                refine ⟨7036998139891996391729713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9382664186522661855639617 7036998139891996391729713)
                ·
                  refine ⟨5277748604918997293797285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7036998139891996391729713 5277748604918997293797285)
                  ·
                    refine ⟨989577863422311992586991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5277748604918997293797285 989577863422311992586991)
                    ·
                      rfl

theorem cell22_2890794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_2890794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890794 prefixEnd_2890794 := by exact prefixLift 2890794
  have htrace : WordTrace (prefixWord ++ tailWord_2890794) baseStart_2890794 baseEnd_2890794 := by
    simpa [prefixWord, tailWord_2890794, baseEnd_2890794] using wordTrace_append hprefix tailTrace_2890794
  have hstable : (prefixWord ++ tailWord_2890794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890794).length < 2 ^ (prefixWord ++ tailWord_2890794).sum := by decide
  have hdescent : baseEnd_2890794 < baseStart_2890794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890805 : List Nat := [1, 3, 3, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2890805 : Nat := 118140960795 + 2890805 * 2 ^ 59
def prefixEnd_2890805 : Nat := 4983230072969 + 3 ^ 40 * 2890805 * 2
def baseEnd_2890805 : Nat := 989581628947111630561957

theorem tailTrace_2890805 : CollatzResearch.WordTrace tailWord_2890805 prefixEnd_2890805 989581628947111630561957 := by
  unfold tailWord_2890805
  simp only [CollatzResearch.WordTrace]
  refine ⟨105436320292114670032833869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70290880194743113355222579 105436320292114670032833869)
  ·
    refine ⟨39538620109543001262312701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105436320292114670032833869 39538620109543001262312701)
    ·
      refine ⟨14826982541078625473367263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39538620109543001262312701 14826982541078625473367263)
      ·
        refine ⟨22240473811617938210050895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14826982541078625473367263 22240473811617938210050895)
        ·
          refine ⟨33360710717426907315076343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22240473811617938210050895 33360710717426907315076343)
          ·
            refine ⟨50041066076140360972614515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33360710717426907315076343 50041066076140360972614515)
            ·
              refine ⟨75061599114210541458921773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50041066076140360972614515 75061599114210541458921773)
              ·
                refine ⟨28148099667828953047095665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75061599114210541458921773 28148099667828953047095665)
                ·
                  refine ⟨21111074750871714785321749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28148099667828953047095665 21111074750871714785321749)
                  ·
                    refine ⟨989581628947111630561957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21111074750871714785321749 989581628947111630561957)
                    ·
                      rfl

theorem cell22_2890805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2890805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890805 prefixEnd_2890805 := by exact prefixLift 2890805
  have htrace : WordTrace (prefixWord ++ tailWord_2890805) baseStart_2890805 baseEnd_2890805 := by
    simpa [prefixWord, tailWord_2890805, baseEnd_2890805] using wordTrace_append hprefix tailTrace_2890805
  have hstable : (prefixWord ++ tailWord_2890805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890805).length < 2 ^ (prefixWord ++ tailWord_2890805).sum := by decide
  have hdescent : baseEnd_2890805 < baseStart_2890805 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890858 : List Nat := [3, 1, 3, 2, 2, 1, 4, 2, 1, 3]
def baseStart_2890858 : Nat := 118140960795 + 2890858 * 2 ^ 59
def prefixEnd_2890858 : Nat := 4983230072969 + 3 ^ 40 * 2890858 * 2
def baseEnd_2890858 : Nat := 989599771930237158986795

theorem tailTrace_2890858 : CollatzResearch.WordTrace tailWord_2890858 prefixEnd_2890858 989599771930237158986795 := by
  unfold tailWord_2890858
  simp only [CollatzResearch.WordTrace]
  refine ⟨26359563340230665021128307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70292168907281773389675485 26359563340230665021128307)
  ·
    refine ⟨39539345010345997531692461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26359563340230665021128307 39539345010345997531692461)
    ·
      refine ⟨14827254378879749074384673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39539345010345997531692461 14827254378879749074384673)
      ·
        refine ⟨11120440784159811805788505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14827254378879749074384673 11120440784159811805788505)
        ·
          refine ⟨8340330588119858854341379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11120440784159811805788505 8340330588119858854341379)
          ·
            refine ⟨12510495882179788281512069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8340330588119858854341379 12510495882179788281512069)
            ·
              refine ⟨2345717977908710302783513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12510495882179788281512069 2345717977908710302783513)
              ·
                refine ⟨1759288483431532727087635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2345717977908710302783513 1759288483431532727087635)
                ·
                  refine ⟨2638932725147299090631453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759288483431532727087635 2638932725147299090631453)
                  ·
                    refine ⟨989599771930237158986795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2638932725147299090631453 989599771930237158986795)
                    ·
                      rfl

theorem cell22_2890858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_2890858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890858 prefixEnd_2890858 := by exact prefixLift 2890858
  have htrace : WordTrace (prefixWord ++ tailWord_2890858) baseStart_2890858 baseEnd_2890858 := by
    simpa [prefixWord, tailWord_2890858, baseEnd_2890858] using wordTrace_append hprefix tailTrace_2890858
  have hstable : (prefixWord ++ tailWord_2890858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890858).length < 2 ^ (prefixWord ++ tailWord_2890858).sum := by decide
  have hdescent : baseEnd_2890858 < baseStart_2890858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890912 : List Nat := [2, 1, 1, 4, 2, 1, 2, 1, 4, 4]
def baseStart_2890912 : Nat := 118140960795 + 2890912 * 2 ^ 59
def prefixEnd_2890912 : Nat := 4983230072969 + 3 ^ 40 * 2890912 * 2
def baseEnd_2890912 : Nat := 989618257233799018136629

theorem tailTrace_2890912 : CollatzResearch.WordTrace tailWord_2890912 prefixEnd_2890912 989618257233799018136629 := by
  unfold tailWord_2890912
  simp only [CollatzResearch.WordTrace]
  refine ⟨52720111451363513653489495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70293481935151351537985993 52720111451363513653489495)
  ·
    refine ⟨79080167177045270480234243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52720111451363513653489495 79080167177045270480234243)
    ·
      refine ⟨118620250765567905720351365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79080167177045270480234243 118620250765567905720351365)
      ·
        refine ⟨22241297018543982322565881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 118620250765567905720351365 22241297018543982322565881)
        ·
          refine ⟨16680972763907986741924411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22241297018543982322565881 16680972763907986741924411)
          ·
            refine ⟨25021459145861980112886617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16680972763907986741924411 25021459145861980112886617)
            ·
              refine ⟨18766094359396485084664963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25021459145861980112886617 18766094359396485084664963)
              ·
                refine ⟨28149141539094727626997445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18766094359396485084664963 28149141539094727626997445)
                ·
                  refine ⟨5277964038580261430062021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28149141539094727626997445 5277964038580261430062021)
                  ·
                    refine ⟨989618257233799018136629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5277964038580261430062021 989618257233799018136629)
                    ·
                      rfl

theorem cell22_2890912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 4, 4].length) (baseStart_2890912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890912 prefixEnd_2890912 := by exact prefixLift 2890912
  have htrace : WordTrace (prefixWord ++ tailWord_2890912) baseStart_2890912 baseEnd_2890912 := by
    simpa [prefixWord, tailWord_2890912, baseEnd_2890912] using wordTrace_append hprefix tailTrace_2890912
  have hstable : (prefixWord ++ tailWord_2890912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890912).length < 2 ^ (prefixWord ++ tailWord_2890912).sum := by decide
  have hdescent : baseEnd_2890912 < baseStart_2890912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2890976 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 3, 3]
def baseStart_2890976 : Nat := 118140960795 + 2890976 * 2 ^ 59
def prefixEnd_2890976 : Nat := 4983230072969 + 3 ^ 40 * 2890976 * 2
def baseEnd_2890976 : Nat := 989640165741724184536433

theorem tailTrace_2890976 : CollatzResearch.WordTrace tailWord_2890976 prefixEnd_2890976 989640165741724184536433 := by
  unfold tailWord_2890976
  simp only [CollatzResearch.WordTrace]
  refine ⟨52721278587247583118654391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70295038116330110824872521 52721278587247583118654391)
  ·
    refine ⟨79081917880871374677981587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 52721278587247583118654391 79081917880871374677981587)
    ·
      refine ⟨118622876821307062016972381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79081917880871374677981587 118622876821307062016972381)
      ·
        refine ⟨44483578807990148256364643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118622876821307062016972381 44483578807990148256364643)
        ·
          refine ⟨66725368211985222384546965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44483578807990148256364643 66725368211985222384546965)
          ·
            refine ⟨3127751634936807299275639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 66725368211985222384546965 3127751634936807299275639)
            ·
              refine ⟨4691627452405210948913459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127751634936807299275639 4691627452405210948913459)
              ·
                refine ⟨7037441178607816423370189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691627452405210948913459 7037441178607816423370189)
                ·
                  refine ⟨2639040441977931158763821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7037441178607816423370189 2639040441977931158763821)
                  ·
                    refine ⟨989640165741724184536433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2639040441977931158763821 989640165741724184536433)
                    ·
                      rfl

theorem cell22_2890976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 3, 3].length) (baseStart_2890976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2890976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2890976 prefixEnd_2890976 := by exact prefixLift 2890976
  have htrace : WordTrace (prefixWord ++ tailWord_2890976) baseStart_2890976 baseEnd_2890976 := by
    simpa [prefixWord, tailWord_2890976, baseEnd_2890976] using wordTrace_append hprefix tailTrace_2890976
  have hstable : (prefixWord ++ tailWord_2890976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2890976).length < 2 ^ (prefixWord ++ tailWord_2890976).sum := by decide
  have hdescent : baseEnd_2890976 < baseStart_2890976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2890976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891038 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 2, 5]
def baseStart_2891038 : Nat := 118140960795 + 2891038 * 2 ^ 59
def prefixEnd_2891038 : Nat := 4983230072969 + 3 ^ 40 * 2891038 * 2
def baseEnd_2891038 : Nat := 989661389608776689486243

theorem tailTrace_2891038 : CollatzResearch.WordTrace tailWord_2891038 prefixEnd_2891038 989661389608776689486243 := by
  unfold tailWord_2891038
  simp only [CollatzResearch.WordTrace]
  refine ⟨13180602312533818853258221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 70296545666847033884043845 13180602312533818853258221)
  ·
    refine ⟨4942725867200182069971833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13180602312533818853258221 4942725867200182069971833)
    ·
      refine ⟨3707044400400136552478875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4942725867200182069971833 3707044400400136552478875)
      ·
        refine ⟨5560566600600204828718313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3707044400400136552478875 5560566600600204828718313)
        ·
          refine ⟨4170424950450153621538735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5560566600600204828718313 4170424950450153621538735)
          ·
            refine ⟨6255637425675230432308103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4170424950450153621538735 6255637425675230432308103)
            ·
              refine ⟨9383456138512845648462155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6255637425675230432308103 9383456138512845648462155)
              ·
                refine ⟨14075184207769268472693233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9383456138512845648462155 14075184207769268472693233)
                ·
                  refine ⟨10556388155826951354519925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14075184207769268472693233 10556388155826951354519925)
                  ·
                    refine ⟨989661389608776689486243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10556388155826951354519925 989661389608776689486243)
                    ·
                      rfl

theorem cell22_2891038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_2891038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891038 prefixEnd_2891038 := by exact prefixLift 2891038
  have htrace : WordTrace (prefixWord ++ tailWord_2891038) baseStart_2891038 baseEnd_2891038 := by
    simpa [prefixWord, tailWord_2891038, baseEnd_2891038] using wordTrace_append hprefix tailTrace_2891038
  have hstable : (prefixWord ++ tailWord_2891038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891038).length < 2 ^ (prefixWord ++ tailWord_2891038).sum := by decide
  have hdescent : baseEnd_2891038 < baseStart_2891038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891077 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 1, 9]
def baseStart_2891077 : Nat := 118140960795 + 2891077 * 2 ^ 59
def prefixEnd_2891077 : Nat := 4983230072969 + 3 ^ 40 * 2891077 * 2
def baseEnd_2891077 : Nat := 989674740105793587761123

theorem tailTrace_2891077 : CollatzResearch.WordTrace tailWord_2891077 prefixEnd_2891077 989674740105793587761123 := by
  unfold tailWord_2891077
  simp only [CollatzResearch.WordTrace]
  refine ⟨105446240947129260486735485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70297493964752840324490323 105446240947129260486735485)
  ·
    refine ⟨39542340355173472682525807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 105446240947129260486735485 39542340355173472682525807)
    ·
      refine ⟨59313510532760209023788711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39542340355173472682525807 59313510532760209023788711)
      ·
        refine ⟨88970265799140313535683067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59313510532760209023788711 88970265799140313535683067)
        ·
          refine ⟨133455398698710470303524601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88970265799140313535683067 133455398698710470303524601)
          ·
            refine ⟨100091549024032852727643451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 133455398698710470303524601 100091549024032852727643451)
            ·
              refine ⟨150137323536049279091465177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100091549024032852727643451 150137323536049279091465177)
              ·
                refine ⟨112602992652036959318598883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 150137323536049279091465177 112602992652036959318598883)
                ·
                  refine ⟨168904488978055438977898325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 112602992652036959318598883 168904488978055438977898325)
                  ·
                    refine ⟨989674740105793587761123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 168904488978055438977898325 989674740105793587761123)
                    ·
                      rfl

theorem cell22_2891077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_2891077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891077 prefixEnd_2891077 := by exact prefixLift 2891077
  have htrace : WordTrace (prefixWord ++ tailWord_2891077) baseStart_2891077 baseEnd_2891077 := by
    simpa [prefixWord, tailWord_2891077, baseEnd_2891077] using wordTrace_append hprefix tailTrace_2891077
  have hstable : (prefixWord ++ tailWord_2891077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891077).length < 2 ^ (prefixWord ++ tailWord_2891077).sum := by decide
  have hdescent : baseEnd_2891077 < baseStart_2891077 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891145 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 3, 3]
def baseStart_2891145 : Nat := 118140960795 + 2891145 * 2 ^ 59
def prefixEnd_2891145 : Nat := 4983230072969 + 3 ^ 40 * 2891145 * 2
def baseEnd_2891145 : Nat := 989698017895464077060915

theorem tailTrace_2891145 : CollatzResearch.WordTrace tailWord_2891145 prefixEnd_2891145 989698017895464077060915 := by
  unfold tailWord_2891145
  simp only [CollatzResearch.WordTrace]
  refine ⟨105448721110882908100210889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70299147407255272066807259 105448721110882908100210889)
  ·
    refine ⟨79086540833162181075158167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105448721110882908100210889 79086540833162181075158167)
    ·
      refine ⟨118629811249743271612737251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79086540833162181075158167 118629811249743271612737251)
      ·
        refine ⟨177944716874614907419105877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118629811249743271612737251 177944716874614907419105877)
        ·
          refine ⟨2085289650874393446317647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 177944716874614907419105877 2085289650874393446317647)
          ·
            refine ⟨3127934476311590169476471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085289650874393446317647 3127934476311590169476471)
            ·
              refine ⟨4691901714467385254214707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3127934476311590169476471 4691901714467385254214707)
              ·
                refine ⟨7037852571701077881322061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4691901714467385254214707 7037852571701077881322061)
                ·
                  refine ⟨2639194714387904205495773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7037852571701077881322061 2639194714387904205495773)
                  ·
                    refine ⟨989698017895464077060915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2639194714387904205495773 989698017895464077060915)
                    ·
                      rfl

theorem cell22_2891145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 3, 3].length) (baseStart_2891145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891145 prefixEnd_2891145 := by exact prefixLift 2891145
  have htrace : WordTrace (prefixWord ++ tailWord_2891145) baseStart_2891145 baseEnd_2891145 := by
    simpa [prefixWord, tailWord_2891145, baseEnd_2891145] using wordTrace_append hprefix tailTrace_2891145
  have hstable : (prefixWord ++ tailWord_2891145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891145).length < 2 ^ (prefixWord ++ tailWord_2891145).sum := by decide
  have hdescent : baseEnd_2891145 < baseStart_2891145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891203 : List Nat := [1, 1, 1, 3, 1, 1, 8, 2, 4]
def baseStart_2891203 : Nat := 118140960795 + 2891203 * 2 ^ 59
def prefixEnd_2891203 : Nat := 4983230072969 + 3 ^ 40 * 2891203 * 2
def baseEnd_2891203 : Nat := 329905957493590419703579

theorem tailTrace_2891203 : CollatzResearch.WordTrace tailWord_2891203 prefixEnd_2891203 329905957493590419703579 := by
  unfold tailWord_2891203
  simp only [CollatzResearch.WordTrace]
  refine ⟨105450836544672784005822263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70300557696448522670548175 105450836544672784005822263)
  ·
    refine ⟨158176254817009176008733395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105450836544672784005822263 158176254817009176008733395)
    ·
      refine ⟨237264382225513764013100093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158176254817009176008733395 237264382225513764013100093)
      ·
        refine ⟨88974143334567661504912535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 237264382225513764013100093 88974143334567661504912535)
        ·
          refine ⟨133461215001851492257368803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88974143334567661504912535 133461215001851492257368803)
          ·
            refine ⟨200191822502777238386053205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133461215001851492257368803 200191822502777238386053205)
            ·
              refine ⟨2345997919954420762336561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 200191822502777238386053205 2345997919954420762336561)
              ·
                refine ⟨1759498439965815571752421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2345997919954420762336561 1759498439965815571752421)
                ·
                  refine ⟨329905957493590419703579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1759498439965815571752421 329905957493590419703579)
                  ·
                    rfl

theorem cell22_2891203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 8, 2, 4].length) (baseStart_2891203 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891203 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891203 prefixEnd_2891203 := by exact prefixLift 2891203
  have htrace : WordTrace (prefixWord ++ tailWord_2891203) baseStart_2891203 baseEnd_2891203 := by
    simpa [prefixWord, tailWord_2891203, baseEnd_2891203] using wordTrace_append hprefix tailTrace_2891203
  have hstable : (prefixWord ++ tailWord_2891203).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891203).length < 2 ^ (prefixWord ++ tailWord_2891203).sum := by decide
  have hdescent : baseEnd_2891203 < baseStart_2891203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891231 : List Nat := [1, 1, 2, 3, 3, 1, 5, 6]
def baseStart_2891231 : Nat := 118140960795 + 2891231 * 2 ^ 59
def prefixEnd_2891231 : Nat := 4983230072969 + 3 ^ 40 * 2891231 * 2
def baseEnd_2891231 : Nat := 109969717494776502156739

theorem tailTrace_2891231 : CollatzResearch.WordTrace tailWord_2891231 prefixEnd_2891231 109969717494776502156739 := by
  unfold tailWord_2891231
  simp only [CollatzResearch.WordTrace]
  refine ⟨105451857788571344787841547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70301238525714229858561031 105451857788571344787841547)
  ·
    refine ⟨158177786682857017181762321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105451857788571344787841547 158177786682857017181762321)
    ·
      refine ⟨118633340012142762886321741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158177786682857017181762321 118633340012142762886321741)
      ·
        refine ⟨44487502504553536082370653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 118633340012142762886321741 44487502504553536082370653)
        ·
          refine ⟨16682813439207576030888995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44487502504553536082370653 16682813439207576030888995)
          ·
            refine ⟨25024220158811364046333493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16682813439207576030888995 25024220158811364046333493)
            ·
              refine ⟨2346020639888565379343765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25024220158811364046333493 2346020639888565379343765)
              ·
                refine ⟨109969717494776502156739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2346020639888565379343765 109969717494776502156739)
                ·
                  rfl

theorem cell22_2891231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 5, 6].length) (baseStart_2891231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891231 prefixEnd_2891231 := by exact prefixLift 2891231
  have htrace : WordTrace (prefixWord ++ tailWord_2891231) baseStart_2891231 baseEnd_2891231 := by
    simpa [prefixWord, tailWord_2891231, baseEnd_2891231] using wordTrace_append hprefix tailTrace_2891231
  have hstable : (prefixWord ++ tailWord_2891231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891231).length < 2 ^ (prefixWord ++ tailWord_2891231).sum := by decide
  have hdescent : baseEnd_2891231 < baseStart_2891231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891233 : List Nat := [1, 2, 3, 1, 2, 5, 1, 1, 2, 4]
def baseStart_2891233 : Nat := 118140960795 + 2891233 * 2 ^ 59
def prefixEnd_2891233 : Nat := 4983230072969 + 3 ^ 40 * 2891233 * 2
def baseEnd_2891233 : Nat := 989728142093861180860645

theorem tailTrace_2891233 : CollatzResearch.WordTrace tailWord_2891233 prefixEnd_2891233 989728142093861180860645 := by
  unfold tailWord_2891233
  simp only [CollatzResearch.WordTrace]
  refine ⟨105451930734564099129414353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70301287156376066086276235 105451930734564099129414353)
  ·
    refine ⟨79088948050923074347060765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105451930734564099129414353 79088948050923074347060765)
    ·
      refine ⟨29658355519096152880147787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79088948050923074347060765 29658355519096152880147787)
      ·
        refine ⟨44487533278644229320221681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29658355519096152880147787 44487533278644229320221681)
        ·
          refine ⟨33365649958983171990166261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44487533278644229320221681 33365649958983171990166261)
          ·
            refine ⟨3128029683654672374078087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33365649958983171990166261 3128029683654672374078087)
            ·
              refine ⟨4692044525482008561117131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128029683654672374078087 4692044525482008561117131)
              ·
                refine ⟨7038066788223012841675697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4692044525482008561117131 7038066788223012841675697)
                ·
                  refine ⟨5278550091167259631256773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7038066788223012841675697 5278550091167259631256773)
                  ·
                    refine ⟨989728142093861180860645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5278550091167259631256773 989728142093861180860645)
                    ·
                      rfl

theorem cell22_2891233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_2891233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891233 prefixEnd_2891233 := by exact prefixLift 2891233
  have htrace : WordTrace (prefixWord ++ tailWord_2891233) baseStart_2891233 baseEnd_2891233 := by
    simpa [prefixWord, tailWord_2891233, baseEnd_2891233] using wordTrace_append hprefix tailTrace_2891233
  have hstable : (prefixWord ++ tailWord_2891233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891233).length < 2 ^ (prefixWord ++ tailWord_2891233).sum := by decide
  have hdescent : baseEnd_2891233 < baseStart_2891233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891244 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 1, 8]
def baseStart_2891244 : Nat := 118140960795 + 2891244 * 2 ^ 59
def prefixEnd_2891244 : Nat := 4983230072969 + 3 ^ 40 * 2891244 * 2
def baseEnd_2891244 : Nat := 989731907618660818835611

theorem tailTrace_2891244 : CollatzResearch.WordTrace tailWord_2891244 prefixEnd_2891244 989731907618660818835611 := by
  unfold tailWord_2891244
  simp only [CollatzResearch.WordTrace]
  refine ⟨52726165968762124004032393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70301554625016165338709857 52726165968762124004032393)
  ·
    refine ⟨39544624476571593003024295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52726165968762124004032393 39544624476571593003024295)
    ·
      refine ⟨59316936714857389504536443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39544624476571593003024295 59316936714857389504536443)
      ·
        refine ⟨88975405072286084256804665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59316936714857389504536443 88975405072286084256804665)
        ·
          refine ⟨66731553804214563192603499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 88975405072286084256804665 66731553804214563192603499)
          ·
            refine ⟨100097330706321844788905249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 66731553804214563192603499 100097330706321844788905249)
            ·
              refine ⟨75072998029741383591678937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100097330706321844788905249 75072998029741383591678937)
              ·
                refine ⟨56304748522306037693759203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75072998029741383591678937 56304748522306037693759203)
                ·
                  refine ⟨84457122783459056540638805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56304748522306037693759203 84457122783459056540638805)
                  ·
                    refine ⟨989731907618660818835611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84457122783459056540638805 989731907618660818835611)
                    ·
                      rfl

theorem cell22_2891244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_2891244 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891244 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891244 prefixEnd_2891244 := by exact prefixLift 2891244
  have htrace : WordTrace (prefixWord ++ tailWord_2891244) baseStart_2891244 baseEnd_2891244 := by
    simpa [prefixWord, tailWord_2891244, baseEnd_2891244] using wordTrace_append hprefix tailTrace_2891244
  have hstable : (prefixWord ++ tailWord_2891244).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891244).length < 2 ^ (prefixWord ++ tailWord_2891244).sum := by decide
  have hdescent : baseEnd_2891244 < baseStart_2891244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891259 : List Nat := [1, 1, 1, 1, 1, 3, 2, 5, 7]
def baseStart_2891259 : Nat := 118140960795 + 2891259 * 2 ^ 59
def prefixEnd_2891259 : Nat := 4983230072969 + 3 ^ 40 * 2891259 * 2
def baseEnd_2891259 : Nat := 329912347475068593236855

theorem tailTrace_2891259 : CollatzResearch.WordTrace tailWord_2891259 prefixEnd_2891259 329912347475068593236855 := by
  unfold tailWord_2891259
  simp only [CollatzResearch.WordTrace]
  refine ⟨105452879032469905569860831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70301919354979937046573887 105452879032469905569860831)
  ·
    refine ⟨158179318548704858354791247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105452879032469905569860831 158179318548704858354791247)
    ·
      refine ⟨237268977823057287532186871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 158179318548704858354791247 237268977823057287532186871)
      ·
        refine ⟨355903466734585931298280307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 237268977823057287532186871 355903466734585931298280307)
        ·
          refine ⟨533855200101878896947420461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 355903466734585931298280307 533855200101878896947420461)
          ·
            refine ⟨200195700038204586355282673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 533855200101878896947420461 200195700038204586355282673)
            ·
              refine ⟨150146775028653439766462005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 200195700038204586355282673 150146775028653439766462005)
              ·
                refine ⟨14076260158936259978105813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 150146775028653439766462005 14076260158936259978105813)
                ·
                  refine ⟨329912347475068593236855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14076260158936259978105813 329912347475068593236855)
                  ·
                    rfl

theorem cell22_2891259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 5, 7].length) (baseStart_2891259 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891259 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891259 prefixEnd_2891259 := by exact prefixLift 2891259
  have htrace : WordTrace (prefixWord ++ tailWord_2891259) baseStart_2891259 baseEnd_2891259 := by
    simpa [prefixWord, tailWord_2891259, baseEnd_2891259] using wordTrace_append hprefix tailTrace_2891259
  have hstable : (prefixWord ++ tailWord_2891259).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891259).length < 2 ^ (prefixWord ++ tailWord_2891259).sum := by decide
  have hdescent : baseEnd_2891259 < baseStart_2891259 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891297 : List Nat := [1, 2, 3, 2, 2, 4, 1, 3, 1, 3]
def baseStart_2891297 : Nat := 118140960795 + 2891297 * 2 ^ 59
def prefixEnd_2891297 : Nat := 4983230072969 + 3 ^ 40 * 2891297 * 2
def baseEnd_2891297 : Nat := 989750050601786347260449

theorem tailTrace_2891297 : CollatzResearch.WordTrace tailWord_2891297 prefixEnd_2891297 989750050601786347260449 := by
  unfold tailWord_2891297
  simp only [CollatzResearch.WordTrace]
  refine ⟨105454265006332238059744145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70302843337554825373162763 105454265006332238059744145)
  ·
    refine ⟨79090698754749178544808109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105454265006332238059744145 79090698754749178544808109)
    ·
      refine ⟨29659012033030941954303041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79090698754749178544808109 29659012033030941954303041)
      ·
        refine ⟨22244259024773206465727281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29659012033030941954303041 22244259024773206465727281)
        ·
          refine ⟨16683194268579904849295461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22244259024773206465727281 16683194268579904849295461)
          ·
            refine ⟨3128098925358732159242899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16683194268579904849295461 3128098925358732159242899)
            ·
              refine ⟨4692148388038098238864349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128098925358732159242899 4692148388038098238864349)
              ·
                refine ⟨1759555645514286839574131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4692148388038098238864349 1759555645514286839574131)
                ·
                  refine ⟨2639333468271430259361197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759555645514286839574131 2639333468271430259361197)
                  ·
                    refine ⟨989750050601786347260449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2639333468271430259361197 989750050601786347260449)
                    ·
                      rfl

theorem cell22_2891297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_2891297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891297 prefixEnd_2891297 := by exact prefixLift 2891297
  have htrace : WordTrace (prefixWord ++ tailWord_2891297) baseStart_2891297 baseEnd_2891297 := by
    simpa [prefixWord, tailWord_2891297, baseEnd_2891297] using wordTrace_append hprefix tailTrace_2891297
  have hstable : (prefixWord ++ tailWord_2891297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891297).length < 2 ^ (prefixWord ++ tailWord_2891297).sum := by decide
  have hdescent : baseEnd_2891297 < baseStart_2891297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891340 : List Nat := [2, 2, 1, 3, 1, 5, 1, 2, 1, 4]
def baseStart_2891340 : Nat := 118140960795 + 2891340 * 2 ^ 59
def prefixEnd_2891340 : Nat := 4983230072969 + 3 ^ 40 * 2891340 * 2
def baseEnd_2891340 : Nat := 989764770380548568435317

theorem tailTrace_2891340 : CollatzResearch.WordTrace tailWord_2891340 prefixEnd_2891340 989764770380548568435317 := by
  unfold tailWord_2891340
  simp only [CollatzResearch.WordTrace]
  refine ⟨52727916672588228201779737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70303888896784304269039649 52727916672588228201779737)
  ·
    refine ⟨39545937504441171151334803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52727916672588228201779737 39545937504441171151334803)
    ·
      refine ⟨59318906256661756727002205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39545937504441171151334803 59318906256661756727002205)
      ·
        refine ⟨22244589846248158772625827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59318906256661756727002205 22244589846248158772625827)
        ·
          refine ⟨33366884769372238158938741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22244589846248158772625827 33366884769372238158938741)
          ·
            refine ⟨3128145447128647327400507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33366884769372238158938741 3128145447128647327400507)
            ·
              refine ⟨4692218170692970991100761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128145447128647327400507 4692218170692970991100761)
              ·
                refine ⟨3519163628019728243325571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4692218170692970991100761 3519163628019728243325571)
                ·
                  refine ⟨5278745442029592364988357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3519163628019728243325571 5278745442029592364988357)
                  ·
                    refine ⟨989764770380548568435317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5278745442029592364988357 989764770380548568435317)
                    ·
                      rfl

theorem cell22_2891340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_2891340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891340 prefixEnd_2891340 := by exact prefixLift 2891340
  have htrace : WordTrace (prefixWord ++ tailWord_2891340) baseStart_2891340 baseEnd_2891340 := by
    simpa [prefixWord, tailWord_2891340, baseEnd_2891340] using wordTrace_append hprefix tailTrace_2891340
  have hstable : (prefixWord ++ tailWord_2891340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891340).length < 2 ^ (prefixWord ++ tailWord_2891340).sum := by decide
  have hdescent : baseEnd_2891340 < baseStart_2891340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891370 : List Nat := [3, 1, 3, 2, 1, 2, 1, 4, 2, 3]
def baseStart_2891370 : Nat := 118140960795 + 2891370 * 2 ^ 59
def prefixEnd_2891370 : Nat := 4983230072969 + 3 ^ 40 * 2891370 * 2
def baseEnd_2891370 : Nat := 989775039993638490185225

theorem tailTrace_2891370 : CollatzResearch.WordTrace tailWord_2891370 prefixEnd_2891370 989775039993638490185225 := by
  unfold tailWord_2891370
  simp only [CollatzResearch.WordTrace]
  refine ⟨26364231883766942881787891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70304618356711847684767709 26364231883766942881787891)
  ·
    refine ⟨39546347825650414322681837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26364231883766942881787891 39546347825650414322681837)
    ·
      refine ⟨14829880434618905371005689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39546347825650414322681837 14829880434618905371005689)
      ·
        refine ⟨11122410325964179028254267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14829880434618905371005689 11122410325964179028254267)
        ·
          refine ⟨16683615488946268542381401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11122410325964179028254267 16683615488946268542381401)
          ·
            refine ⟨12512711616709701406786051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16683615488946268542381401 12512711616709701406786051)
            ·
              refine ⟨18769067425064552110179077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12512711616709701406786051 18769067425064552110179077)
              ·
                refine ⟨3519200142199603520658577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18769067425064552110179077 3519200142199603520658577)
                ·
                  refine ⟨2639400106649702640493933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3519200142199603520658577 2639400106649702640493933)
                  ·
                    refine ⟨989775039993638490185225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2639400106649702640493933 989775039993638490185225)
                    ·
                      rfl

theorem cell22_2891370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 4, 2, 3].length) (baseStart_2891370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891370 prefixEnd_2891370 := by exact prefixLift 2891370
  have htrace : WordTrace (prefixWord ++ tailWord_2891370) baseStart_2891370 baseEnd_2891370 := by
    simpa [prefixWord, tailWord_2891370, baseEnd_2891370] using wordTrace_append hprefix tailTrace_2891370
  have hstable : (prefixWord ++ tailWord_2891370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891370).length < 2 ^ (prefixWord ++ tailWord_2891370).sum := by decide
  have hdescent : baseEnd_2891370 < baseStart_2891370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891428 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 7]
def baseStart_2891428 : Nat := 118140960795 + 2891428 * 2 ^ 59
def prefixEnd_2891428 : Nat := 4983230072969 + 3 ^ 40 * 2891428 * 2
def baseEnd_2891428 : Nat := 329931631526315224078349

theorem tailTrace_2891428 : CollatzResearch.WordTrace tailWord_2891428 prefixEnd_2891428 329931631526315224078349 := by
  unfold tailWord_2891428
  simp only [CollatzResearch.WordTrace]
  refine ⟨52729521484428823716381469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70306028645905098288508625 52729521484428823716381469)
  ·
    refine ⟨19773570556660808893643051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 52729521484428823716381469 19773570556660808893643051)
    ·
      refine ⟨29660355834991213340464577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19773570556660808893643051 29660355834991213340464577)
      ·
        refine ⟨22245266876243410005348433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29660355834991213340464577 22245266876243410005348433)
        ·
          refine ⟨16683950157182557504011325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22245266876243410005348433 16683950157182557504011325)
          ·
            refine ⟨6256481308943459064004247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16683950157182557504011325 6256481308943459064004247)
            ·
              refine ⟨9384721963415188596006371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6256481308943459064004247 9384721963415188596006371)
              ·
                refine ⟨14077082945122782894009557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9384721963415188596006371 14077082945122782894009557)
                ·
                  refine ⟨329931631526315224078349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14077082945122782894009557 329931631526315224078349)
                  ·
                    rfl

theorem cell22_2891428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_2891428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891428 prefixEnd_2891428 := by exact prefixLift 2891428
  have htrace : WordTrace (prefixWord ++ tailWord_2891428) baseStart_2891428 baseEnd_2891428 := by
    simpa [prefixWord, tailWord_2891428, baseEnd_2891428] using wordTrace_append hprefix tailTrace_2891428
  have hstable : (prefixWord ++ tailWord_2891428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891428).length < 2 ^ (prefixWord ++ tailWord_2891428).sum := by decide
  have hdescent : baseEnd_2891428 < baseStart_2891428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891462 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 7]
def baseStart_2891462 : Nat := 118140960795 + 2891462 * 2 ^ 59
def prefixEnd_2891462 : Nat := 4983230072969 + 3 ^ 40 * 2891462 * 2
def baseEnd_2891462 : Nat := 329935511157926972294981

theorem tailTrace_2891462 : CollatzResearch.WordTrace tailWord_2891462 prefixEnd_2891462 329935511157926972294981 := by
  unfold tailWord_2891462
  simp only [CollatzResearch.WordTrace]
  refine ⟨3295633845335452226234395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 70306855367156314159667093 3295633845335452226234395)
  ·
    refine ⟨4943450768003178339351593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3295633845335452226234395 4943450768003178339351593)
    ·
      refine ⟨3707588076002383754513695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4943450768003178339351593 3707588076002383754513695)
      ·
        refine ⟨5561382114003575631770543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3707588076002383754513695 5561382114003575631770543)
        ·
          refine ⟨8342073171005363447655815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5561382114003575631770543 8342073171005363447655815)
          ·
            refine ⟨12513109756508045171483723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8342073171005363447655815 12513109756508045171483723)
            ·
              refine ⟨18769664634762067757225585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12513109756508045171483723 18769664634762067757225585)
              ·
                refine ⟨14077248476071550817919189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18769664634762067757225585 14077248476071550817919189)
                ·
                  refine ⟨329935511157926972294981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14077248476071550817919189 329935511157926972294981)
                  ·
                    rfl

theorem cell22_2891462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_2891462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891462 prefixEnd_2891462 := by exact prefixLift 2891462
  have htrace : WordTrace (prefixWord ++ tailWord_2891462) baseStart_2891462 baseEnd_2891462 := by
    simpa [prefixWord, tailWord_2891462, baseEnd_2891462] using wordTrace_append hprefix tailTrace_2891462
  have hstable : (prefixWord ++ tailWord_2891462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891462).length < 2 ^ (prefixWord ++ tailWord_2891462).sum := by decide
  have hdescent : baseEnd_2891462 < baseStart_2891462 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891466 : List Nat := [3, 1, 2, 1, 6, 1, 1, 3, 1, 3]
def baseStart_2891466 : Nat := 118140960795 + 2891466 * 2 ^ 59
def prefixEnd_2891466 : Nat := 4983230072969 + 3 ^ 40 * 2891466 * 2
def baseEnd_2891466 : Nat := 989807902755526239784931

theorem tailTrace_2891466 : CollatzResearch.WordTrace tailWord_2891466 prefixEnd_2891466 989807902755526239784931 := by
  unfold tailWord_2891466
  simp only [CollatzResearch.WordTrace]
  refine ⟨26365107235679994980661563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70306952628479986615097501 26365107235679994980661563)
  ·
    refine ⟨39547660853519992470992345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26365107235679994980661563 39547660853519992470992345)
    ·
      refine ⟨29660745640139994353244259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39547660853519992470992345 29660745640139994353244259)
      ·
        refine ⟨44491118460209991529866389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29660745640139994353244259 44491118460209991529866389)
        ·
          refine ⟨2085521177822343352962487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 44491118460209991529866389 2085521177822343352962487)
          ·
            refine ⟨3128281766733515029443731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085521177822343352962487 3128281766733515029443731)
            ·
              refine ⟨4692422650100272544165597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3128281766733515029443731 4692422650100272544165597)
              ·
                refine ⟨1759658493787602204062099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4692422650100272544165597 1759658493787602204062099)
                ·
                  refine ⟨2639487740681403306093149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1759658493787602204062099 2639487740681403306093149)
                  ·
                    refine ⟨989807902755526239784931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2639487740681403306093149 989807902755526239784931)
                    ·
                      rfl

theorem cell22_2891466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 3, 1, 3].length) (baseStart_2891466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891466 prefixEnd_2891466 := by exact prefixLift 2891466
  have htrace : WordTrace (prefixWord ++ tailWord_2891466) baseStart_2891466 baseEnd_2891466 := by
    simpa [prefixWord, tailWord_2891466, baseEnd_2891466] using wordTrace_append hprefix tailTrace_2891466
  have hstable : (prefixWord ++ tailWord_2891466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891466).length < 2 ^ (prefixWord ++ tailWord_2891466).sum := by decide
  have hdescent : baseEnd_2891466 < baseStart_2891466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891503 : List Nat := [1, 1, 2, 1, 5, 1, 1, 2, 4, 4]
def baseStart_2891503 : Nat := 118140960795 + 2891503 * 2 ^ 59
def prefixEnd_2891503 : Nat := 4983230072969 + 3 ^ 40 * 2891503 * 2
def baseEnd_2891503 : Nat := 989820568611670476609817

theorem tailTrace_2891503 : CollatzResearch.WordTrace tailWord_2891503 prefixEnd_2891503 989820568611670476609817 := by
  unfold tailWord_2891503
  simp only [CollatzResearch.WordTrace]
  refine ⟨105461778443585935241743163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70307852295723956827828775 105461778443585935241743163)
  ·
    refine ⟨158192667665378902862614745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 105461778443585935241743163 158192667665378902862614745)
    ·
      refine ⟨118644500749034177146961059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 158192667665378902862614745 118644500749034177146961059)
      ·
        refine ⟨177966751123551265720441589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118644500749034177146961059 177966751123551265720441589)
        ·
          refine ⟨16684382917832931161291399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177966751123551265720441589 16684382917832931161291399)
          ·
            refine ⟨25026574376749396741937099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16684382917832931161291399 25026574376749396741937099)
            ·
              refine ⟨37539861565124095112905649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25026574376749396741937099 37539861565124095112905649)
              ·
                refine ⟨28154896173843071334679237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37539861565124095112905649 28154896173843071334679237)
                ·
                  refine ⟨5279043032595575875252357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28154896173843071334679237 5279043032595575875252357)
                  ·
                    refine ⟨989820568611670476609817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5279043032595575875252357 989820568611670476609817)
                    ·
                      rfl

theorem cell22_2891503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_2891503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891503 prefixEnd_2891503 := by exact prefixLift 2891503
  have htrace : WordTrace (prefixWord ++ tailWord_2891503) baseStart_2891503 baseEnd_2891503 := by
    simpa [prefixWord, tailWord_2891503, baseEnd_2891503] using wordTrace_append hprefix tailTrace_2891503
  have hstable : (prefixWord ++ tailWord_2891503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891503).length < 2 ^ (prefixWord ++ tailWord_2891503).sum := by decide
  have hdescent : baseEnd_2891503 < baseStart_2891503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891548 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 1, 8]
def baseStart_2891548 : Nat := 118140960795 + 2891548 * 2 ^ 59
def prefixEnd_2891548 : Nat := 4983230072969 + 3 ^ 40 * 2891548 * 2
def baseEnd_2891548 : Nat := 989835973031305359234679

theorem tailTrace_2891548 : CollatzResearch.WordTrace tailWord_2891548 prefixEnd_2891548 989835973031305359234679 := by
  unfold tailWord_2891548
  simp only [CollatzResearch.WordTrace]
  refine ⟨52731709864211453963565649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 70308946485615271951420865 52731709864211453963565649)
  ·
    refine ⟨39548782398158590472674237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 52731709864211453963565649 39548782398158590472674237)
    ·
      refine ⟨14830793399309471427252839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39548782398158590472674237 14830793399309471427252839)
      ·
        refine ⟨22246190098964207140879259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14830793399309471427252839 22246190098964207140879259)
        ·
          refine ⟨33369285148446310711318889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22246190098964207140879259 33369285148446310711318889)
          ·
            refine ⟨25026963861334733033489167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33369285148446310711318889 25026963861334733033489167)
            ·
              refine ⟨37540445792002099550233751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25026963861334733033489167 37540445792002099550233751)
              ·
                refine ⟨56310668688003149325350627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37540445792002099550233751 56310668688003149325350627)
                ·
                  refine ⟨84466003032004723988025941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56310668688003149325350627 84466003032004723988025941)
                  ·
                    refine ⟨989835973031305359234679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 84466003032004723988025941 989835973031305359234679)
                    ·
                      rfl

theorem cell22_2891548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_2891548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891548 prefixEnd_2891548 := by exact prefixLift 2891548
  have htrace : WordTrace (prefixWord ++ tailWord_2891548) baseStart_2891548 baseEnd_2891548 := by
    simpa [prefixWord, tailWord_2891548, baseEnd_2891548] using wordTrace_append hprefix tailTrace_2891548
  have hstable : (prefixWord ++ tailWord_2891548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891548).length < 2 ^ (prefixWord ++ tailWord_2891548).sum := by decide
  have hdescent : baseEnd_2891548 < baseStart_2891548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891597 : List Nat := [1, 6, 1, 2, 1, 2, 1, 1, 7]
def baseStart_2891597 : Nat := 118140960795 + 2891597 * 2 ^ 59
def prefixEnd_2891597 : Nat := 4983230072969 + 3 ^ 40 * 2891597 * 2
def baseEnd_2891597 : Nat := 329950915577561854919843

theorem tailTrace_2891597 : CollatzResearch.WordTrace tailWord_2891597 prefixEnd_2891597 329950915577561854919843 := by
  unfold tailWord_2891597
  simp only [CollatzResearch.WordTrace]
  refine ⟨105465206905245389295665045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70310137936830259530443363 105465206905245389295665045)
  ·
    refine ⟨4943681573683377623234299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 105465206905245389295665045 4943681573683377623234299)
    ·
      refine ⟨7415522360525066434851449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4943681573683377623234299 7415522360525066434851449)
      ·
        refine ⟨5561641770393799826138587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7415522360525066434851449 5561641770393799826138587)
        ·
          refine ⟨8342462655590699739207881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5561641770393799826138587 8342462655590699739207881)
          ·
            refine ⟨6256846991693024804405911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8342462655590699739207881 6256846991693024804405911)
            ·
              refine ⟨9385270487539537206608867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6256846991693024804405911 9385270487539537206608867)
              ·
                refine ⟨14077905731309305809913301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9385270487539537206608867 14077905731309305809913301)
                ·
                  refine ⟨329950915577561854919843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14077905731309305809913301 329950915577561854919843)
                  ·
                    rfl

theorem cell22_2891597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_2891597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891597 prefixEnd_2891597 := by exact prefixLift 2891597
  have htrace : WordTrace (prefixWord ++ tailWord_2891597) baseStart_2891597 baseEnd_2891597 := by
    simpa [prefixWord, tailWord_2891597, baseEnd_2891597] using wordTrace_append hprefix tailTrace_2891597
  have hstable : (prefixWord ++ tailWord_2891597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891597).length < 2 ^ (prefixWord ++ tailWord_2891597).sum := by decide
  have hdescent : baseEnd_2891597 < baseStart_2891597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891642 : List Nat := [3, 1, 1, 1, 1, 1, 7, 3, 4]
def baseStart_2891642 : Nat := 118140960795 + 2891642 * 2 ^ 59
def prefixEnd_2891642 : Nat := 4983230072969 + 3 ^ 40 * 2891642 * 2
def baseEnd_2891642 : Nat := 329956050384106815794797

theorem tailTrace_2891642 : CollatzResearch.WordTrace tailWord_2891642 prefixEnd_2891642 329956050384106815794797 := by
  unfold tailWord_2891642
  simp only [CollatzResearch.WordTrace]
  refine ⟨26366712047520590495263295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70311232126721574654035453 26366712047520590495263295)
  ·
    refine ⟨39550068071280885742894943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26366712047520590495263295 39550068071280885742894943)
    ·
      refine ⟨59325102106921328614342415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39550068071280885742894943 59325102106921328614342415)
      ·
        refine ⟨88987653160381992921513623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59325102106921328614342415 88987653160381992921513623)
        ·
          refine ⟨133481479740572989382270435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 88987653160381992921513623 133481479740572989382270435)
          ·
            refine ⟨200222219610859484073405653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 133481479740572989382270435 200222219610859484073405653)
            ·
              refine ⟨4692708272129519157970445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 200222219610859484073405653 4692708272129519157970445)
              ·
                refine ⟨1759765602048569684238917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4692708272129519157970445 1759765602048569684238917)
                ·
                  refine ⟨329956050384106815794797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1759765602048569684238917 329956050384106815794797)
                  ·
                    rfl

theorem cell22_2891642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 3, 4].length) (baseStart_2891642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891642 prefixEnd_2891642 := by exact prefixLift 2891642
  have htrace : WordTrace (prefixWord ++ tailWord_2891642) baseStart_2891642 baseEnd_2891642 := by
    simpa [prefixWord, tailWord_2891642, baseEnd_2891642] using wordTrace_append hprefix tailTrace_2891642
  have hstable : (prefixWord ++ tailWord_2891642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891642).length < 2 ^ (prefixWord ++ tailWord_2891642).sum := by decide
  have hdescent : baseEnd_2891642 < baseStart_2891642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891657 : List Nat := [1, 2, 1, 1, 5, 1, 2, 4, 2, 3]
def baseStart_2891657 : Nat := 118140960795 + 2891657 * 2 ^ 59
def prefixEnd_2891657 : Nat := 4983230072969 + 3 ^ 40 * 2891657 * 2
def baseEnd_2891657 : Nat := 989873285958865408259345

theorem tailTrace_2891657 : CollatzResearch.WordTrace tailWord_2891657 prefixEnd_2891657 989873285958865408259345 := by
  unfold tailWord_2891657
  simp only [CollatzResearch.WordTrace]
  refine ⟨105467395285028019542849225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 70311596856685346361899483 105467395285028019542849225)
  ·
    refine ⟨79100546463771014657136919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 105467395285028019542849225 79100546463771014657136919)
    ·
      refine ⟨118650819695656521985705379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79100546463771014657136919 118650819695656521985705379)
      ·
        refine ⟨177976229543484782978558069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 118650819695656521985705379 177976229543484782978558069)
        ·
          refine ⟨16685271519701698404239819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 177976229543484782978558069 16685271519701698404239819)
          ·
            refine ⟨25027907279552547606359729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16685271519701698404239819 25027907279552547606359729)
            ·
              refine ⟨18770930459664410704769797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25027907279552547606359729 18770930459664410704769797)
              ·
                refine ⟨3519549461187077007144337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18770930459664410704769797 3519549461187077007144337)
                ·
                  refine ⟨2639662095890307755358253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3519549461187077007144337 2639662095890307755358253)
                  ·
                    refine ⟨989873285958865408259345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2639662095890307755358253 989873285958865408259345)
                    ·
                      rfl

theorem cell22_2891657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 4, 2, 3].length) (baseStart_2891657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891657 prefixEnd_2891657 := by exact prefixLift 2891657
  have htrace : WordTrace (prefixWord ++ tailWord_2891657) baseStart_2891657 baseEnd_2891657 := by
    simpa [prefixWord, tailWord_2891657, baseEnd_2891657] using wordTrace_append hprefix tailTrace_2891657
  have hstable : (prefixWord ++ tailWord_2891657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891657).length < 2 ^ (prefixWord ++ tailWord_2891657).sum := by decide
  have hdescent : baseEnd_2891657 < baseStart_2891657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2891674 : List Nat := [3, 1, 1, 4, 2, 2, 1, 3, 2, 3]
def baseStart_2891674 : Nat := 118140960795 + 2891674 * 2 ^ 59
def prefixEnd_2891674 : Nat := 4983230072969 + 3 ^ 40 * 2891674 * 2
def baseEnd_2891674 : Nat := 989879105406283030584293

theorem tailTrace_2891674 : CollatzResearch.WordTrace tailWord_2891674 prefixEnd_2891674 989879105406283030584293 := by
  unfold tailWord_2891674
  simp only [CollatzResearch.WordTrace]
  refine ⟨26367003831491607861554519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 70312010217310954297478717 26367003831491607861554519)
  ·
    refine ⟨39550505747237411792331779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26367003831491607861554519 39550505747237411792331779)
    ·
      refine ⟨59325758620856117688497669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39550505747237411792331779 59325758620856117688497669)
      ·
        refine ⟨11123579741410522066593313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59325758620856117688497669 11123579741410522066593313)
        ·
          refine ⟨8342684806057891549944985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11123579741410522066593313 8342684806057891549944985)
          ·
            refine ⟨6257013604543418662458739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8342684806057891549944985 6257013604543418662458739)
            ·
              refine ⟨9385520406815127993688109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6257013604543418662458739 9385520406815127993688109)
              ·
                refine ⟨3519570152555672997633041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9385520406815127993688109 3519570152555672997633041)
                ·
                  refine ⟨2639677614416754748224781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3519570152555672997633041 2639677614416754748224781)
                  ·
                    refine ⟨989879105406283030584293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2639677614416754748224781 989879105406283030584293)
                    ·
                      rfl

theorem cell22_2891674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 3, 2, 3].length) (baseStart_2891674 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2891674 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2891674 prefixEnd_2891674 := by exact prefixLift 2891674
  have htrace : WordTrace (prefixWord ++ tailWord_2891674) baseStart_2891674 baseEnd_2891674 := by
    simpa [prefixWord, tailWord_2891674, baseEnd_2891674] using wordTrace_append hprefix tailTrace_2891674
  have hstable : (prefixWord ++ tailWord_2891674).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2891674).length < 2 ^ (prefixWord ++ tailWord_2891674).sum := by decide
  have hdescent : baseEnd_2891674 < baseStart_2891674 := by decide
  rcases family_descends (prefixWord ++ tailWord_2891674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
