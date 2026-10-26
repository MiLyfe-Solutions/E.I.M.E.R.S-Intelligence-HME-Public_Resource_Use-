import V185TrunkScan23Chunk1357

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8042174 : List Nat := [4, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_8042174 : Nat := 118140960795 + 8042174 * 2 ^ 59
def prefixEnd_8042174 : Nat := 4983230072969 + 3 ^ 40 * 8042174 * 2
def baseEnd_8042174 : Nat := 4129500769091523190939721

theorem tailTrace_8042174 : CollatzResearch.WordTrace tailWord_8042174 prefixEnd_8042174 4129500769091523190939721 := by
  unfold tailWord_8042174
  simp only [CollatzResearch.WordTrace]
  refine ⟨36665272895823070851858697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195548122111056377876579717 36665272895823070851858697)
  ·
    refine ⟨27498954671867303138894023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36665272895823070851858697 27498954671867303138894023)
    ·
      refine ⟨41248432007800954708341035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27498954671867303138894023 41248432007800954708341035)
      ·
        refine ⟨61872648011701432062511553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41248432007800954708341035 61872648011701432062511553)
        ·
          refine ⟨46404486008776074046883665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61872648011701432062511553 46404486008776074046883665)
          ·
            refine ⟨34803364506582055535162749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46404486008776074046883665 34803364506582055535162749)
            ·
              refine ⟨13051261689968270825686031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34803364506582055535162749 13051261689968270825686031)
              ·
                refine ⟨19576892534952406238529047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13051261689968270825686031 19576892534952406238529047)
                ·
                  refine ⟨29365338802428609357793571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19576892534952406238529047 29365338802428609357793571)
                  ·
                    refine ⟨44048008203642914036690357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29365338802428609357793571 44048008203642914036690357)
                    ·
                      refine ⟨4129500769091523190939721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44048008203642914036690357 4129500769091523190939721)
                      ·
                        rfl

theorem cell23_8042174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_8042174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042174 prefixEnd_8042174 := by exact prefixLift 8042174
  have htrace : WordTrace (prefixWord ++ tailWord_8042174) baseStart_8042174 baseEnd_8042174 := by
    simpa [prefixWord, tailWord_8042174, baseEnd_8042174] using wordTrace_append hprefix tailTrace_8042174
  have hstable : (prefixWord ++ tailWord_8042174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042174).length < 2 ^ (prefixWord ++ tailWord_8042174).sum := by decide
  have hdescent : baseEnd_8042174 < baseStart_8042174 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042182 : List Nat := [6, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3]
def baseStart_8042182 : Nat := 118140960795 + 8042182 * 2 ^ 59
def prefixEnd_8042182 : Nat := 4983230072969 + 3 ^ 40 * 8042182 * 2
def baseEnd_8042182 : Nat := 4129504876936759159639685

theorem tailTrace_8042182 : CollatzResearch.WordTrace tailWord_8042182 prefixEnd_8042182 4129504876936759159639685 := by
  unfold tailWord_8042182
  simp only [CollatzResearch.WordTrace]
  refine ⟨9166327342204862005661275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 195548316633703722787440533 9166327342204862005661275)
  ·
    refine ⟨13749491013307293008491913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9166327342204862005661275 13749491013307293008491913)
    ·
      refine ⟨10312118259980469756368935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13749491013307293008491913 10312118259980469756368935)
      ·
        refine ⟨15468177389970704634553403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10312118259980469756368935 15468177389970704634553403)
        ·
          refine ⟨23202266084956056951830105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15468177389970704634553403 23202266084956056951830105)
          ·
            refine ⟨17401699563717042713872579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23202266084956056951830105 17401699563717042713872579)
            ·
              refine ⟨26102549345575564070808869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17401699563717042713872579 26102549345575564070808869)
              ·
                refine ⟨4894228002295418263276663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26102549345575564070808869 4894228002295418263276663)
                ·
                  refine ⟨7341342003443127394914995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4894228002295418263276663 7341342003443127394914995)
                  ·
                    refine ⟨11012013005164691092372493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7341342003443127394914995 11012013005164691092372493)
                    ·
                      refine ⟨4129504876936759159639685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11012013005164691092372493 4129504876936759159639685)
                      ·
                        rfl

theorem cell23_8042182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_8042182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042182 prefixEnd_8042182 := by exact prefixLift 8042182
  have htrace : WordTrace (prefixWord ++ tailWord_8042182) baseStart_8042182 baseEnd_8042182 := by
    simpa [prefixWord, tailWord_8042182, baseEnd_8042182] using wordTrace_append hprefix tailTrace_8042182
  have hstable : (prefixWord ++ tailWord_8042182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042182).length < 2 ^ (prefixWord ++ tailWord_8042182).sum := by decide
  have hdescent : baseEnd_8042182 < baseStart_8042182 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042194 : List Nat := [3, 2, 2, 2, 2, 3, 1, 8]
def baseStart_8042194 : Nat := 118140960795 + 8042194 * 2 ^ 59
def prefixEnd_8042194 : Nat := 4983230072969 + 3 ^ 40 * 8042194 * 2
def baseEnd_8042194 : Nat := 152944853285356041210727

theorem tailTrace_8042194 : CollatzResearch.WordTrace tailWord_8042194 prefixEnd_8042194 152944853285356041210727 := by
  unfold tailWord_8042194
  simp only [CollatzResearch.WordTrace]
  refine ⟨73330728156628027557649409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195548608417674740153731757 73330728156628027557649409)
  ·
    refine ⟨54998046117471020668237057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73330728156628027557649409 54998046117471020668237057)
    ·
      refine ⟨41248534588103265501177793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 54998046117471020668237057 41248534588103265501177793)
      ·
        refine ⟨30936400941077449125883345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41248534588103265501177793 30936400941077449125883345)
        ·
          refine ⟨23202300705808086844412509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30936400941077449125883345 23202300705808086844412509)
          ·
            refine ⟨8700862764678032566654691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23202300705808086844412509 8700862764678032566654691)
            ·
              refine ⟨13051294147017048849982037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8700862764678032566654691 13051294147017048849982037)
              ·
                refine ⟨152944853285356041210727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13051294147017048849982037 152944853285356041210727)
                ·
                  rfl

theorem cell23_8042194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 3, 1, 8].length) (baseStart_8042194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042194 prefixEnd_8042194 := by exact prefixLift 8042194
  have htrace : WordTrace (prefixWord ++ tailWord_8042194) baseStart_8042194 baseEnd_8042194 := by
    simpa [prefixWord, tailWord_8042194, baseEnd_8042194] using wordTrace_append hprefix tailTrace_8042194
  have hstable : (prefixWord ++ tailWord_8042194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042194).length < 2 ^ (prefixWord ++ tailWord_8042194).sum := by decide
  have hdescent : baseEnd_8042194 < baseStart_8042194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042198 : List Nat := [5, 2, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_8042198 : Nat := 118140960795 + 8042198 * 2 ^ 59
def prefixEnd_8042198 : Nat := 4983230072969 + 3 ^ 40 * 8042198 * 2
def baseEnd_8042198 : Nat := 1376504364209077032346537

theorem tailTrace_8042198 : CollatzResearch.WordTrace tailWord_8042198 prefixEnd_8042198 1376504364209077032346537 := by
  unfold tailWord_8042198
  simp only [CollatzResearch.WordTrace]
  refine ⟨18332691157406101182108953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195548705678998412609162165 18332691157406101182108953)
  ·
    refine ⟨13749518368054575886581715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18332691157406101182108953 13749518368054575886581715)
    ·
      refine ⟨20624277552081863829872573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13749518368054575886581715 20624277552081863829872573)
      ·
        refine ⟨7734104082030698936202215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20624277552081863829872573 7734104082030698936202215)
        ·
          refine ⟨11601156123046048404303323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734104082030698936202215 11601156123046048404303323)
          ·
            refine ⟨17401734184569072606454985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601156123046048404303323 17401734184569072606454985)
            ·
              refine ⟨13051300638426804454841239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17401734184569072606454985 13051300638426804454841239)
              ·
                refine ⟨19576950957640206682261859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13051300638426804454841239 19576950957640206682261859)
                ·
                  refine ⟨29365426436460310023392789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19576950957640206682261859 29365426436460310023392789)
                  ·
                    refine ⟨1376504364209077032346537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29365426436460310023392789 1376504364209077032346537)
                    ·
                      rfl

theorem cell23_8042198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_8042198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042198 prefixEnd_8042198 := by exact prefixLift 8042198
  have htrace : WordTrace (prefixWord ++ tailWord_8042198) baseStart_8042198 baseEnd_8042198 := by
    simpa [prefixWord, tailWord_8042198, baseEnd_8042198] using wordTrace_append hprefix tailTrace_8042198
  have hstable : (prefixWord ++ tailWord_8042198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042198).length < 2 ^ (prefixWord ++ tailWord_8042198).sum := by decide
  have hdescent : baseEnd_8042198 < baseStart_8042198 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042205 : List Nat := [1, 4, 3, 3, 1, 1, 1, 2, 3, 2, 2]
def baseStart_8042205 : Nat := 118140960795 + 8042205 * 2 ^ 59
def prefixEnd_8042205 : Nat := 4983230072969 + 3 ^ 40 * 8042205 * 2
def baseEnd_8042205 : Nat := 4129516686991812569652079

theorem tailTrace_8042205 : CollatzResearch.WordTrace tailWord_8042205 prefixEnd_8042205 4129516686991812569652079 := by
  unfold tailWord_8042205
  simp only [CollatzResearch.WordTrace]
  refine ⟨293323313829472259109248069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195548875886314839406165379 293323313829472259109248069)
  ·
    refine ⟨54998121343026048582984013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293323313829472259109248069 54998121343026048582984013)
    ·
      refine ⟨20624295503634768218619005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 54998121343026048582984013 20624295503634768218619005)
      ·
        refine ⟨7734110813863038081982127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20624295503634768218619005 7734110813863038081982127)
        ·
          refine ⟨11601166220794557122973191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734110813863038081982127 11601166220794557122973191)
          ·
            refine ⟨17401749331191835684459787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601166220794557122973191 17401749331191835684459787)
            ·
              refine ⟨26102623996787753526689681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17401749331191835684459787 26102623996787753526689681)
              ·
                refine ⟨19576967997590815145017261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26102623996787753526689681 19576967997590815145017261)
                ·
                  refine ⟨7341362999096555679381473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19576967997590815145017261 7341362999096555679381473)
                  ·
                    refine ⟨5506022249322416759536105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7341362999096555679381473 5506022249322416759536105)
                    ·
                      refine ⟨4129516686991812569652079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506022249322416759536105 4129516686991812569652079)
                      ·
                        rfl

theorem cell23_8042205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_8042205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042205 prefixEnd_8042205 := by exact prefixLift 8042205
  have htrace : WordTrace (prefixWord ++ tailWord_8042205) baseStart_8042205 baseEnd_8042205 := by
    simpa [prefixWord, tailWord_8042205, baseEnd_8042205] using wordTrace_append hprefix tailTrace_8042205
  have hstable : (prefixWord ++ tailWord_8042205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042205).length < 2 ^ (prefixWord ++ tailWord_8042205).sum := by decide
  have hdescent : baseEnd_8042205 < baseStart_8042205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042238 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_8042238 : Nat := 118140960795 + 8042238 * 2 ^ 59
def prefixEnd_8042238 : Nat := 4983230072969 + 3 ^ 40 * 8042238 * 2
def baseEnd_8042238 : Nat := 4129533631853410940539427

theorem tailTrace_8042238 : CollatzResearch.WordTrace tailWord_8042238 prefixEnd_8042238 4129533631853410940539427 := by
  unfold tailWord_8042238
  simp only [CollatzResearch.WordTrace]
  refine ⟨36665564679794088218149921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195549678292235137163466245 36665564679794088218149921)
  ·
    refine ⟨27499173509845566163612441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36665564679794088218149921 27499173509845566163612441)
    ·
      refine ⟨20624380132384174622709331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27499173509845566163612441 20624380132384174622709331)
      ·
        refine ⟨30936570198576261934063997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20624380132384174622709331 30936570198576261934063997)
        ·
          refine ⟨11601213824466098225273999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30936570198576261934063997 11601213824466098225273999)
          ·
            refine ⟨17401820736699147337910999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601213824466098225273999 17401820736699147337910999)
            ·
              refine ⟨26102731105048721006866499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17401820736699147337910999 26102731105048721006866499)
              ·
                refine ⟨39154096657573081510299749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26102731105048721006866499 39154096657573081510299749)
                ·
                  refine ⟨7341393123294952783181203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39154096657573081510299749 7341393123294952783181203)
                  ·
                    refine ⟨11012089684942429174771805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7341393123294952783181203 11012089684942429174771805)
                    ·
                      refine ⟨4129533631853410940539427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11012089684942429174771805 4129533631853410940539427)
                      ·
                        rfl

theorem cell23_8042238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_8042238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042238 prefixEnd_8042238 := by exact prefixLift 8042238
  have htrace : WordTrace (prefixWord ++ tailWord_8042238) baseStart_8042238 baseEnd_8042238 := by
    simpa [prefixWord, tailWord_8042238, baseEnd_8042238] using wordTrace_append hprefix tailTrace_8042238
  have hstable : (prefixWord ++ tailWord_8042238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042238).length < 2 ^ (prefixWord ++ tailWord_8042238).sum := by decide
  have hdescent : baseEnd_8042238 < baseStart_8042238 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042261 : List Nat := [1, 3, 2, 1, 2, 3, 3, 1, 1, 4, 2]
def baseStart_8042261 : Nat := 118140960795 + 8042261 * 2 ^ 59
def prefixEnd_8042261 : Nat := 4983230072969 + 3 ^ 40 * 8042261 * 2
def baseEnd_8042261 : Nat := 4129545441908464350551821

theorem tailTrace_8042261 : CollatzResearch.WordTrace tailWord_8042261 prefixEnd_8042261 4129545441908464350551821 := by
  unfold tailWord_8042261
  simp only [CollatzResearch.WordTrace]
  refine ⟨293325356317269380673286637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195550237544846253782191091 293325356317269380673286637)
  ·
    refine ⟨109997008618976017752482489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293325356317269380673286637 109997008618976017752482489)
    ·
      refine ⟨82497756464232013314361867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109997008618976017752482489 82497756464232013314361867)
      ·
        refine ⟨123746634696348019971542801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82497756464232013314361867 123746634696348019971542801)
        ·
          refine ⟨92809976022261014978657101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123746634696348019971542801 92809976022261014978657101)
          ·
            refine ⟨34803741008347880616996413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92809976022261014978657101 34803741008347880616996413)
            ·
              refine ⟨13051402878130455231373655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34803741008347880616996413 13051402878130455231373655)
              ·
                refine ⟨19577104317195682847060483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13051402878130455231373655 19577104317195682847060483)
                ·
                  refine ⟨29365656475793524270590725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19577104317195682847060483 29365656475793524270590725)
                  ·
                    refine ⟨5506060589211285800735761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29365656475793524270590725 5506060589211285800735761)
                    ·
                      refine ⟨4129545441908464350551821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506060589211285800735761 4129545441908464350551821)
                      ·
                        rfl

theorem cell23_8042261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_8042261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042261 prefixEnd_8042261 := by exact prefixLift 8042261
  have htrace : WordTrace (prefixWord ++ tailWord_8042261) baseStart_8042261 baseEnd_8042261 := by
    simpa [prefixWord, tailWord_8042261, baseEnd_8042261] using wordTrace_append hprefix tailTrace_8042261
  have hstable : (prefixWord ++ tailWord_8042261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042261).length < 2 ^ (prefixWord ++ tailWord_8042261).sum := by decide
  have hdescent : baseEnd_8042261 < baseStart_8042261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042301 : List Nat := [1, 4, 1, 4, 1, 3, 1, 1, 7]
def baseStart_8042301 : Nat := 118140960795 + 8042301 * 2 ^ 59
def prefixEnd_8042301 : Nat := 4983230072969 + 3 ^ 40 * 8042301 * 2
def baseEnd_8042301 : Nat := 458840664570516021561293

theorem tailTrace_8042301 : CollatzResearch.WordTrace tailWord_8042301 prefixEnd_8042301 458840664570516021561293 := by
  unfold tailWord_8042301
  simp only [CollatzResearch.WordTrace]
  refine ⟨293326815237124467504742757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195551210158082978336495171 293326815237124467504742757)
  ·
    refine ⟨54998777856960837657139267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293326815237124467504742757 54998777856960837657139267)
    ·
      refine ⟨82498166785441256485708901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54998777856960837657139267 82498166785441256485708901)
      ·
        refine ⟨15468406272270235591070419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82498166785441256485708901 15468406272270235591070419)
        ·
          refine ⟨23202609408405353386605629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15468406272270235591070419 23202609408405353386605629)
          ·
            refine ⟨8700978528152007519977111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23202609408405353386605629 8700978528152007519977111)
            ·
              refine ⟨13051467792228011279965667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8700978528152007519977111 13051467792228011279965667)
              ·
                refine ⟨19577201688342016919948501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13051467792228011279965667 19577201688342016919948501)
                ·
                  refine ⟨458840664570516021561293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19577201688342016919948501 458840664570516021561293)
                  ·
                    rfl

theorem cell23_8042301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 1, 7].length) (baseStart_8042301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042301 prefixEnd_8042301 := by exact prefixLift 8042301
  have htrace : WordTrace (prefixWord ++ tailWord_8042301) baseStart_8042301 baseEnd_8042301 := by
    simpa [prefixWord, tailWord_8042301, baseEnd_8042301] using wordTrace_append hprefix tailTrace_8042301
  have hstable : (prefixWord ++ tailWord_8042301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042301).length < 2 ^ (prefixWord ++ tailWord_8042301).sum := by decide
  have hdescent : baseEnd_8042301 < baseStart_8042301 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042307 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 7]
def baseStart_8042307 : Nat := 118140960795 + 8042307 * 2 ^ 59
def prefixEnd_8042307 : Nat := 4983230072969 + 3 ^ 40 * 8042307 * 2
def baseEnd_8042307 : Nat := 4129569062018571170576609

theorem tailTrace_8042307 : CollatzResearch.WordTrace tailWord_8042307 prefixEnd_8042307 4129569062018571170576609 := by
  unfold tailWord_8042307
  simp only [CollatzResearch.WordTrace]
  refine ⟨293327034075102730529461175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195551356050068487019640783 293327034075102730529461175)
  ·
    refine ⟨439990551112654095794191763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293327034075102730529461175 439990551112654095794191763)
    ·
      refine ⟨659985826668981143691287645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439990551112654095794191763 659985826668981143691287645)
      ·
        refine ⟨247494685000867928884232867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 659985826668981143691287645 247494685000867928884232867)
        ·
          refine ⟨371242027501301893326349301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247494685000867928884232867 371242027501301893326349301)
          ·
            refine ⟨34803940078247052499345247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 371242027501301893326349301 34803940078247052499345247)
            ·
              refine ⟨52205910117370578749017871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34803940078247052499345247 52205910117370578749017871)
              ·
                refine ⟨78308865176055868123526807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52205910117370578749017871 78308865176055868123526807)
                ·
                  refine ⟨117463297764083802185290211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78308865176055868123526807 117463297764083802185290211)
                  ·
                    refine ⟨176194946646125703277935317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117463297764083802185290211 176194946646125703277935317)
                    ·
                      refine ⟨4129569062018571170576609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176194946646125703277935317 4129569062018571170576609)
                      ·
                        rfl

theorem cell23_8042307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 1, 1, 7].length) (baseStart_8042307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042307 prefixEnd_8042307 := by exact prefixLift 8042307
  have htrace : WordTrace (prefixWord ++ tailWord_8042307) baseStart_8042307 baseEnd_8042307 := by
    simpa [prefixWord, tailWord_8042307, baseEnd_8042307] using wordTrace_append hprefix tailTrace_8042307
  have hstable : (prefixWord ++ tailWord_8042307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042307).length < 2 ^ (prefixWord ++ tailWord_8042307).sum := by decide
  have hdescent : baseEnd_8042307 < baseStart_8042307 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042347 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 6]
def baseStart_8042347 : Nat := 118140960795 + 8042347 * 2 ^ 59
def prefixEnd_8042347 : Nat := 4983230072969 + 3 ^ 40 * 8042347 * 2
def baseEnd_8042347 : Nat := 4129589601244751014076425

theorem tailTrace_8042347 : CollatzResearch.WordTrace tailWord_8042347 prefixEnd_8042347 4129589601244751014076425 := by
  unfold tailWord_8042347
  simp only [CollatzResearch.WordTrace]
  refine ⟨293328492994957817360917295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195552328663305211573944863 293328492994957817360917295)
  ·
    refine ⟨439992739492436726041375943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293328492994957817360917295 439992739492436726041375943)
    ·
      refine ⟨659989109238655089062063915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439992739492436726041375943 659989109238655089062063915)
      ·
        refine ⟨989983663857982633593095873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659989109238655089062063915 989983663857982633593095873)
        ·
          refine ⟨742487747893486975194821905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989983663857982633593095873 742487747893486975194821905)
          ·
            refine ⟨556865810920115231396116429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742487747893486975194821905 556865810920115231396116429)
            ·
              refine ⟨208824679095043211773543661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556865810920115231396116429 208824679095043211773543661)
              ·
                refine ⟨78309254660641204415078873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208824679095043211773543661 78309254660641204415078873)
                ·
                  refine ⟨58731940995480903311309155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78309254660641204415078873 58731940995480903311309155)
                  ·
                    refine ⟨88097911493221354966963733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58731940995480903311309155 88097911493221354966963733)
                    ·
                      refine ⟨4129589601244751014076425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88097911493221354966963733 4129589601244751014076425)
                      ·
                        rfl

theorem cell23_8042347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 1, 6].length) (baseStart_8042347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042347 prefixEnd_8042347 := by exact prefixLift 8042347
  have htrace : WordTrace (prefixWord ++ tailWord_8042347) baseStart_8042347 baseEnd_8042347 := by
    simpa [prefixWord, tailWord_8042347, baseEnd_8042347] using wordTrace_append hprefix tailTrace_8042347
  have hstable : (prefixWord ++ tailWord_8042347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042347).length < 2 ^ (prefixWord ++ tailWord_8042347).sum := by decide
  have hdescent : baseEnd_8042347 < baseStart_8042347 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042354 : List Nat := [3, 2, 1, 2, 1, 1, 1, 2, 3, 4, 3]
def baseStart_8042354 : Nat := 118140960795 + 8042354 * 2 ^ 59
def prefixEnd_8042354 : Nat := 4983230072969 + 3 ^ 40 * 8042354 * 2
def baseEnd_8042354 : Nat := 4129593195609332486688893

theorem tailTrace_8042354 : CollatzResearch.WordTrace tailWord_8042354 prefixEnd_8042354 4129593195609332486688893 := by
  unfold tailWord_8042354
  simp only [CollatzResearch.WordTrace]
  refine ⟨73332187076483114389105529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195552498870621638370948077 73332187076483114389105529)
  ·
    refine ⟨54999140307362335791829147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73332187076483114389105529 54999140307362335791829147)
    ·
      refine ⟨82498710461043503687743721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 54999140307362335791829147 82498710461043503687743721)
      ·
        refine ⟨61874032845782627765807791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82498710461043503687743721 61874032845782627765807791)
        ·
          refine ⟨92811049268673941648711687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61874032845782627765807791 92811049268673941648711687)
          ·
            refine ⟨139216573903010912473067531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92811049268673941648711687 139216573903010912473067531)
            ·
              refine ⟨208824860854516368709601297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139216573903010912473067531 208824860854516368709601297)
              ·
                refine ⟨156618645640887276532200973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208824860854516368709601297 156618645640887276532200973)
                ·
                  refine ⟨58731992115332728699575365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156618645640887276532200973 58731992115332728699575365)
                  ·
                    refine ⟨11012248521624886631170381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58731992115332728699575365 11012248521624886631170381)
                    ·
                      refine ⟨4129593195609332486688893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11012248521624886631170381 4129593195609332486688893)
                      ·
                        rfl

theorem cell23_8042354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 2, 3, 4, 3].length) (baseStart_8042354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042354 prefixEnd_8042354 := by exact prefixLift 8042354
  have htrace : WordTrace (prefixWord ++ tailWord_8042354) baseStart_8042354 baseEnd_8042354 := by
    simpa [prefixWord, tailWord_8042354, baseEnd_8042354] using wordTrace_append hprefix tailTrace_8042354
  have hstable : (prefixWord ++ tailWord_8042354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042354).length < 2 ^ (prefixWord ++ tailWord_8042354).sum := by decide
  have hdescent : baseEnd_8042354 < baseStart_8042354 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042378 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 3, 4]
def baseStart_8042378 : Nat := 118140960795 + 8042378 * 2 ^ 59
def prefixEnd_8042378 : Nat := 4983230072969 + 3 ^ 40 * 8042378 * 2
def baseEnd_8042378 : Nat := 1376535173048346797596261

theorem tailTrace_8042378 : CollatzResearch.WordTrace tailWord_8042378 prefixEnd_8042378 1376535173048346797596261 := by
  unfold tailWord_8042378
  simp only [CollatzResearch.WordTrace]
  refine ⟨73332405914461377413823947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195553082438563673103530525 73332405914461377413823947)
  ·
    refine ⟨109998608871692066120735921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73332405914461377413823947 109998608871692066120735921)
    ·
      refine ⟨82498956653769049590551941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 109998608871692066120735921 82498956653769049590551941)
      ·
        refine ⟨15468554372581696798228489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82498956653769049590551941 15468554372581696798228489)
        ·
          refine ⟨11601415779436272598671367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15468554372581696798228489 11601415779436272598671367)
          ·
            refine ⟨17402123669154408898007051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601415779436272598671367 17402123669154408898007051)
            ·
              refine ⟨26103185503731613347010577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17402123669154408898007051 26103185503731613347010577)
              ·
                refine ⟨19577389127798710010257933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26103185503731613347010577 19577389127798710010257933)
                ·
                  refine ⟨7341520922924516253846725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19577389127798710010257933 7341520922924516253846725)
                  ·
                    refine ⟨1376535173048346797596261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7341520922924516253846725 1376535173048346797596261)
                    ·
                      rfl

theorem cell23_8042378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 3, 4].length) (baseStart_8042378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042378 prefixEnd_8042378 := by exact prefixLift 8042378
  have htrace : WordTrace (prefixWord ++ tailWord_8042378) baseStart_8042378 baseEnd_8042378 := by
    simpa [prefixWord, tailWord_8042378, baseEnd_8042378] using wordTrace_append hprefix tailTrace_8042378
  have hstable : (prefixWord ++ tailWord_8042378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042378).length < 2 ^ (prefixWord ++ tailWord_8042378).sum := by decide
  have hdescent : baseEnd_8042378 < baseStart_8042378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042388 : List Nat := [2, 4, 2, 1, 1, 2, 3, 1, 2, 2, 3]
def baseStart_8042388 : Nat := 118140960795 + 8042388 * 2 ^ 59
def prefixEnd_8042388 : Nat := 4983230072969 + 3 ^ 40 * 8042388 * 2
def baseEnd_8042388 : Nat := 4129610653951585353663737

theorem tailTrace_8042388 : CollatzResearch.WordTrace tailWord_8042388 prefixEnd_8042388 4129610653951585353663737 := by
  unfold tailWord_8042388
  simp only [CollatzResearch.WordTrace]
  refine ⟨146664994193904640681579909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195553325591872854242106545 146664994193904640681579909)
  ·
    refine ⟨27499686411357120127796233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146664994193904640681579909 27499686411357120127796233)
    ·
      refine ⟨20624764808517840095847175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27499686411357120127796233 20624764808517840095847175)
      ·
        refine ⟨30937147212776760143770763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20624764808517840095847175 30937147212776760143770763)
        ·
          refine ⟨46405720819165140215656145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30937147212776760143770763 46405720819165140215656145)
          ·
            refine ⟨34804290614373855161742109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46405720819165140215656145 34804290614373855161742109)
            ·
              refine ⟨13051608980390195685653291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34804290614373855161742109 13051608980390195685653291)
              ·
                refine ⟨19577413470585293528479937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13051608980390195685653291 19577413470585293528479937)
                ·
                  refine ⟨14683060102938970146359953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19577413470585293528479937 14683060102938970146359953)
                  ·
                    refine ⟨11012295077204227609769965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14683060102938970146359953 11012295077204227609769965)
                    ·
                      refine ⟨4129610653951585353663737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11012295077204227609769965 4129610653951585353663737)
                      ·
                        rfl

theorem cell23_8042388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 1, 2, 2, 3].length) (baseStart_8042388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042388 prefixEnd_8042388 := by exact prefixLift 8042388
  have htrace : WordTrace (prefixWord ++ tailWord_8042388) baseStart_8042388 baseEnd_8042388 := by
    simpa [prefixWord, tailWord_8042388, baseEnd_8042388] using wordTrace_append hprefix tailTrace_8042388
  have hstable : (prefixWord ++ tailWord_8042388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042388).length < 2 ^ (prefixWord ++ tailWord_8042388).sum := by decide
  have hdescent : baseEnd_8042388 < baseStart_8042388 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042408 : List Nat := [2, 1, 6, 2, 1, 1, 1, 1, 8]
def baseStart_8042408 : Nat := 118140960795 + 8042408 * 2 ^ 59
def prefixEnd_8042408 : Nat := 4983230072969 + 3 ^ 40 * 8042408 * 2
def baseEnd_8042408 : Nat := 458846769284963919490405

theorem tailTrace_8042408 : CollatzResearch.WordTrace tailWord_8042408 prefixEnd_8042408 458846769284963919490405 := by
  unfold tailWord_8042408
  simp only [CollatzResearch.WordTrace]
  refine ⟨146665358923868412389443939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195553811898491216519258585 146665358923868412389443939)
  ·
    refine ⟨219998038385802618584165909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146665358923868412389443939 219998038385802618584165909)
    ·
      refine ⟨10312408049334497746132777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 219998038385802618584165909 10312408049334497746132777)
      ·
        refine ⟨7734306037000873309599583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10312408049334497746132777 7734306037000873309599583)
        ·
          refine ⟨11601459055501309964399375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734306037000873309599583 11601459055501309964399375)
          ·
            refine ⟨17402188583251964946599063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601459055501309964399375 17402188583251964946599063)
            ·
              refine ⟨26103282874877947419898595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17402188583251964946599063 26103282874877947419898595)
              ·
                refine ⟨39154924312316921129847893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26103282874877947419898595 39154924312316921129847893)
                ·
                  refine ⟨458846769284963919490405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39154924312316921129847893 458846769284963919490405)
                  ·
                    rfl

theorem cell23_8042408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 1, 1, 8].length) (baseStart_8042408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042408 prefixEnd_8042408 := by exact prefixLift 8042408
  have htrace : WordTrace (prefixWord ++ tailWord_8042408) baseStart_8042408 baseEnd_8042408 := by
    simpa [prefixWord, tailWord_8042408, baseEnd_8042408] using wordTrace_append hprefix tailTrace_8042408
  have hstable : (prefixWord ++ tailWord_8042408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042408).length < 2 ^ (prefixWord ++ tailWord_8042408).sum := by decide
  have hdescent : baseEnd_8042408 < baseStart_8042408 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042475 : List Nat := [1, 1, 1, 1, 2, 3, 1, 8, 1, 2, 2]
def baseStart_8042475 : Nat := 118140960795 + 8042475 * 2 ^ 59
def prefixEnd_8042475 : Nat := 4983230072969 + 3 ^ 40 * 8042475 * 2
def baseEnd_8042475 : Nat := 4129655326768526513275837

theorem tailTrace_8042475 : CollatzResearch.WordTrace tailWord_8042475 prefixEnd_8042475 4129655326768526513275837 := by
  unfold tailWord_8042475
  simp only [CollatzResearch.WordTrace]
  refine ⟨293333161538494095221576879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195555441025662730147717919 293333161538494095221576879)
  ·
    refine ⟨439999742307741142832365319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293333161538494095221576879 439999742307741142832365319)
    ·
      refine ⟨659999613461611714248547979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439999742307741142832365319 659999613461611714248547979)
      ·
        refine ⟨989999420192417571372821969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 659999613461611714248547979 989999420192417571372821969)
        ·
          refine ⟨742499565144313178529616477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 989999420192417571372821969 742499565144313178529616477)
          ·
            refine ⟨278437336929117441948606179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 742499565144313178529616477 278437336929117441948606179)
            ·
              refine ⟨417656005393676162922909269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278437336929117441948606179 417656005393676162922909269)
              ·
                refine ⟨4894406313207142534252843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 417656005393676162922909269 4894406313207142534252843)
                ·
                  refine ⟨7341609469810713801379265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4894406313207142534252843 7341609469810713801379265)
                  ·
                    refine ⟨5506207102358035351034449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7341609469810713801379265 5506207102358035351034449)
                    ·
                      refine ⟨4129655326768526513275837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506207102358035351034449 4129655326768526513275837)
                      ·
                        rfl

theorem cell23_8042475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 8, 1, 2, 2].length) (baseStart_8042475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042475 prefixEnd_8042475 := by exact prefixLift 8042475
  have htrace : WordTrace (prefixWord ++ tailWord_8042475) baseStart_8042475 baseEnd_8042475 := by
    simpa [prefixWord, tailWord_8042475, baseEnd_8042475] using wordTrace_append hprefix tailTrace_8042475
  have hstable : (prefixWord ++ tailWord_8042475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042475).length < 2 ^ (prefixWord ++ tailWord_8042475).sum := by decide
  have hdescent : baseEnd_8042475 < baseStart_8042475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042481 : List Nat := [1, 2, 2, 2, 5, 1, 2, 8]
def baseStart_8042481 : Nat := 118140960795 + 8042481 * 2 ^ 59
def prefixEnd_8042481 : Nat := 4983230072969 + 3 ^ 40 * 8042481 * 2
def baseEnd_8042481 : Nat := 152950311394535314437067

theorem tailTrace_8042481 : CollatzResearch.WordTrace tailWord_8042481 prefixEnd_8042481 152950311394535314437067 := by
  unfold tailWord_8042481
  simp only [CollatzResearch.WordTrace]
  refine ⟨293333380376472358246295297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195555586917648238830863531 293333380376472358246295297)
  ·
    refine ⟨220000035282354268684721473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293333380376472358246295297 220000035282354268684721473)
    ·
      refine ⟨165000026461765701513541105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220000035282354268684721473 165000026461765701513541105)
      ·
        refine ⟨123750019846324276135155829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165000026461765701513541105 123750019846324276135155829)
        ·
          refine ⟨11601564360592900887670859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123750019846324276135155829 11601564360592900887670859)
          ·
            refine ⟨17402346540889351331506289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601564360592900887670859 17402346540889351331506289)
            ·
              refine ⟨13051759905667013498629717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17402346540889351331506289 13051759905667013498629717)
              ·
                refine ⟨152950311394535314437067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13051759905667013498629717 152950311394535314437067)
                ·
                  rfl

theorem cell23_8042481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 2, 8].length) (baseStart_8042481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042481 prefixEnd_8042481 := by exact prefixLift 8042481
  have htrace : WordTrace (prefixWord ++ tailWord_8042481) baseStart_8042481 baseEnd_8042481 := by
    simpa [prefixWord, tailWord_8042481, baseEnd_8042481] using wordTrace_append hprefix tailTrace_8042481
  have hstable : (prefixWord ++ tailWord_8042481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042481).length < 2 ^ (prefixWord ++ tailWord_8042481).sum := by decide
  have hdescent : baseEnd_8042481 < baseStart_8042481 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042525 : List Nat := [1, 4, 2, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_8042525 : Nat := 118140960795 + 8042525 * 2 ^ 59
def prefixEnd_8042525 : Nat := 4983230072969 + 3 ^ 40 * 8042525 * 2
def baseEnd_8042525 : Nat := 4129681000801251317650607

theorem tailTrace_8042525 : CollatzResearch.WordTrace tailWord_8042525 prefixEnd_8042525 4129681000801251317650607 := by
  unfold tailWord_8042525
  simp only [CollatzResearch.WordTrace]
  refine ⟨293334985188312953760897029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195556656792208635840598019 293334985188312953760897029)
  ·
    refine ⟨55000309722808678830168193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293334985188312953760897029 55000309722808678830168193)
    ·
      refine ⟨41250232292106509122626145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55000309722808678830168193 41250232292106509122626145)
      ·
        refine ⟨30937674219079881841969609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41250232292106509122626145 30937674219079881841969609)
        ·
          refine ⟨23203255664309911381477207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30937674219079881841969609 23203255664309911381477207)
          ·
            refine ⟨34804883496464867072215811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23203255664309911381477207 34804883496464867072215811)
            ·
              refine ⟨52207325244697300608323717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34804883496464867072215811 52207325244697300608323717)
              ·
                refine ⟨9788873483380743864060697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52207325244697300608323717 9788873483380743864060697)
                ·
                  refine ⟨7341655112535557898045523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9788873483380743864060697 7341655112535557898045523)
                  ·
                    refine ⟨11012482668803336847068285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7341655112535557898045523 11012482668803336847068285)
                    ·
                      refine ⟨4129681000801251317650607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11012482668803336847068285 4129681000801251317650607)
                      ·
                        rfl

theorem cell23_8042525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_8042525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042525 prefixEnd_8042525 := by exact prefixLift 8042525
  have htrace : WordTrace (prefixWord ++ tailWord_8042525) baseStart_8042525 baseEnd_8042525 := by
    simpa [prefixWord, tailWord_8042525, baseEnd_8042525] using wordTrace_append hprefix tailTrace_8042525
  have hstable : (prefixWord ++ tailWord_8042525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042525).length < 2 ^ (prefixWord ++ tailWord_8042525).sum := by decide
  have hdescent : baseEnd_8042525 < baseStart_8042525 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042588 : List Nat := [2, 2, 4, 1, 1, 3, 2, 1, 7]
def baseStart_8042588 : Nat := 118140960795 + 8042588 * 2 ^ 59
def prefixEnd_8042588 : Nat := 4983230072969 + 3 ^ 40 * 8042588 * 2
def baseEnd_8042588 : Nat := 458857038898053841240313

theorem tailTrace_8042588 : CollatzResearch.WordTrace tailWord_8042588 prefixEnd_8042588 458857038898053841240313 := by
  unfold tailWord_8042588
  simp only [CollatzResearch.WordTrace]
  refine ⟨146668641493542357760220209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195558188658056477013626945 146668641493542357760220209)
  ·
    refine ⟨110001481120156768320165157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146668641493542357760220209 110001481120156768320165157)
    ·
      refine ⟨20625277710029394060030967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110001481120156768320165157 20625277710029394060030967)
      ·
        refine ⟨30937916565044091090046451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20625277710029394060030967 30937916565044091090046451)
        ·
          refine ⟨46406874847566136635069677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30937916565044091090046451 46406874847566136635069677)
          ·
            refine ⟨17402578067837301238151129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46406874847566136635069677 17402578067837301238151129)
            ·
              refine ⟨13051933550877975928613347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17402578067837301238151129 13051933550877975928613347)
              ·
                refine ⟨19577900326316963892920021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13051933550877975928613347 19577900326316963892920021)
                ·
                  refine ⟨458857038898053841240313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19577900326316963892920021 458857038898053841240313)
                  ·
                    rfl

theorem cell23_8042588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_8042588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042588 prefixEnd_8042588 := by exact prefixLift 8042588
  have htrace : WordTrace (prefixWord ++ tailWord_8042588) baseStart_8042588 baseEnd_8042588 := by
    simpa [prefixWord, tailWord_8042588, baseEnd_8042588] using wordTrace_append hprefix tailTrace_8042588
  have hstable : (prefixWord ++ tailWord_8042588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042588).length < 2 ^ (prefixWord ++ tailWord_8042588).sum := by decide
  have hdescent : baseEnd_8042588 < baseStart_8042588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042641 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 3]
def baseStart_8042641 : Nat := 118140960795 + 8042641 * 2 ^ 59
def prefixEnd_8042641 : Nat := 4983230072969 + 3 ^ 40 * 8042641 * 2
def baseEnd_8042641 : Nat := 4129740564557172863800073

theorem tailTrace_8042641 : CollatzResearch.WordTrace tailWord_8042641 prefixEnd_8042641 4129740564557172863800073 := by
  unfold tailWord_8042641
  simp only [CollatzResearch.WordTrace]
  refine ⟨293339216055892705572119777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195559477370595137048079851 293339216055892705572119777)
  ·
    refine ⟨220004412041919529179089833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293339216055892705572119777 220004412041919529179089833)
    ·
      refine ⟨165003309031439646884317375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220004412041919529179089833 165003309031439646884317375)
      ·
        refine ⟨247504963547159470326476063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165003309031439646884317375 247504963547159470326476063)
        ·
          refine ⟨371257445320739205489714095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247504963547159470326476063 371257445320739205489714095)
          ·
            refine ⟨556886167981108808234571143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371257445320739205489714095 556886167981108808234571143)
            ·
              refine ⟨835329251971663212351856715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556886167981108808234571143 835329251971663212351856715)
              ·
                refine ⟨1252993877957494818527785073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835329251971663212351856715 1252993877957494818527785073)
                ·
                  refine ⟨939745408468121113895838805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1252993877957494818527785073 939745408468121113895838805)
                  ·
                    refine ⟨11012641505485794303466861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 939745408468121113895838805 11012641505485794303466861)
                    ·
                      refine ⟨4129740564557172863800073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11012641505485794303466861 4129740564557172863800073)
                      ·
                        rfl

theorem cell23_8042641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 3].length) (baseStart_8042641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042641 prefixEnd_8042641 := by exact prefixLift 8042641
  have htrace : WordTrace (prefixWord ++ tailWord_8042641) baseStart_8042641 baseEnd_8042641 := by
    simpa [prefixWord, tailWord_8042641, baseEnd_8042641] using wordTrace_append hprefix tailTrace_8042641
  have hstable : (prefixWord ++ tailWord_8042641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042641).length < 2 ^ (prefixWord ++ tailWord_8042641).sum := by decide
  have hdescent : baseEnd_8042641 < baseStart_8042641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042742 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 1, 5]
def baseStart_8042742 : Nat := 118140960795 + 8042742 * 2 ^ 59
def prefixEnd_8042742 : Nat := 4983230072969 + 3 ^ 40 * 8042742 * 2
def baseEnd_8042742 : Nat := 1376597475367758989545703

theorem tailTrace_8042742 : CollatzResearch.WordTrace tailWord_8042742 prefixEnd_8042742 1376597475367758989545703 := by
  unfold tailWord_8042742
  simp only [CollatzResearch.WordTrace]
  refine ⟨18333931239282924988846655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195561933219017866547697653 18333931239282924988846655)
  ·
    refine ⟨27500896858924387483269983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18333931239282924988846655 27500896858924387483269983)
    ·
      refine ⟨41251345288386581224904975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27500896858924387483269983 41251345288386581224904975)
      ·
        refine ⟨61877017932579871837357463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41251345288386581224904975 61877017932579871837357463)
        ·
          refine ⟨92815526898869807756036195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61877017932579871837357463 92815526898869807756036195)
          ·
            refine ⟨139223290348304711634054293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92815526898869807756036195 139223290348304711634054293)
            ·
              refine ⟨6526091735076783357846295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139223290348304711634054293 6526091735076783357846295)
              ·
                refine ⟨9789137602615175036769443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526091735076783357846295 9789137602615175036769443)
                ·
                  refine ⟨14683706403922762555154165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9789137602615175036769443 14683706403922762555154165)
                  ·
                    refine ⟨1376597475367758989545703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14683706403922762555154165 1376597475367758989545703)
                    ·
                      rfl

theorem cell23_8042742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 1, 5].length) (baseStart_8042742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042742 prefixEnd_8042742 := by exact prefixLift 8042742
  have htrace : WordTrace (prefixWord ++ tailWord_8042742) baseStart_8042742 baseEnd_8042742 := by
    simpa [prefixWord, tailWord_8042742, baseEnd_8042742] using wordTrace_append hprefix tailTrace_8042742
  have hstable : (prefixWord ++ tailWord_8042742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042742).length < 2 ^ (prefixWord ++ tailWord_8042742).sum := by decide
  have hdescent : baseEnd_8042742 < baseStart_8042742 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042751 : List Nat := [1, 1, 2, 2, 1, 4, 12]
def baseStart_8042751 : Nat := 118140960795 + 8042751 * 2 ^ 59
def prefixEnd_8042751 : Nat := 4983230072969 + 3 ^ 40 * 8042751 * 2
def baseEnd_8042751 : Nat := 50985148733693425104007

theorem tailTrace_8042751 : CollatzResearch.WordTrace tailWord_8042751 prefixEnd_8042751 50985148733693425104007 := by
  unfold tailWord_8042751
  simp only [CollatzResearch.WordTrace]
  refine ⟨293343228085494194358624107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195562152056996129572416071 293343228085494194358624107)
  ·
    refine ⟨440014842128241291537936161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293343228085494194358624107 440014842128241291537936161)
    ·
      refine ⟨330011131596180968653452121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440014842128241291537936161 330011131596180968653452121)
      ·
        refine ⟨247508348697135726490089091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330011131596180968653452121 247508348697135726490089091)
        ·
          refine ⟨371262523045703589735133637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247508348697135726490089091 371262523045703589735133637)
          ·
            refine ⟨69611723071069423075337557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 371262523045703589735133637 69611723071069423075337557)
            ·
              refine ⟨50985148733693425104007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 69611723071069423075337557 50985148733693425104007)
              ·
                rfl

theorem cell23_8042751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 12].length) (baseStart_8042751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042751 prefixEnd_8042751 := by exact prefixLift 8042751
  have htrace : WordTrace (prefixWord ++ tailWord_8042751) baseStart_8042751 baseEnd_8042751 := by
    simpa [prefixWord, tailWord_8042751, baseEnd_8042751] using wordTrace_append hprefix tailTrace_8042751
  have hstable : (prefixWord ++ tailWord_8042751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042751).length < 2 ^ (prefixWord ++ tailWord_8042751).sum := by decide
  have hdescent : baseEnd_8042751 < baseStart_8042751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042762 : List Nat := [3, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2]
def baseStart_8042762 : Nat := 118140960795 + 8042762 * 2 ^ 59
def prefixEnd_8042762 : Nat := 4983230072969 + 3 ^ 40 * 8042762 * 2
def baseEnd_8042762 : Nat := 4129802695716366890387017

theorem tailTrace_8042762 : CollatzResearch.WordTrace tailWord_8042762 prefixEnd_8042762 4129802695716366890387017 := by
  unfold tailWord_8042762
  simp only [CollatzResearch.WordTrace]
  refine ⟨73335907322113585809318635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195562419525636228824849693 73335907322113585809318635)
  ·
    refine ⟨110003860983170378713977953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73335907322113585809318635 110003860983170378713977953)
    ·
      refine ⟨82502895737377784035483465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110003860983170378713977953 82502895737377784035483465)
      ·
        refine ⟨61877171803033338026612599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82502895737377784035483465 61877171803033338026612599)
        ·
          refine ⟨92815757704550007039918899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61877171803033338026612599 92815757704550007039918899)
          ·
            refine ⟨139223636556825010559878349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92815757704550007039918899 139223636556825010559878349)
            ·
              refine ⟨52208863708809378959954381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139223636556825010559878349 52208863708809378959954381)
              ·
                refine ⟨19578323890803517109982893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52208863708809378959954381 19578323890803517109982893)
                ·
                  refine ⟨7341871459051318916243585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19578323890803517109982893 7341871459051318916243585)
                  ·
                    refine ⟨5506403594288489187182689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7341871459051318916243585 5506403594288489187182689)
                    ·
                      refine ⟨4129802695716366890387017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506403594288489187182689 4129802695716366890387017)
                      ·
                        rfl

theorem cell23_8042762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2].length) (baseStart_8042762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042762 prefixEnd_8042762 := by exact prefixLift 8042762
  have htrace : WordTrace (prefixWord ++ tailWord_8042762) baseStart_8042762 baseEnd_8042762 := by
    simpa [prefixWord, tailWord_8042762, baseEnd_8042762] using wordTrace_append hprefix tailTrace_8042762
  have hstable : (prefixWord ++ tailWord_8042762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042762).length < 2 ^ (prefixWord ++ tailWord_8042762).sum := by decide
  have hdescent : baseEnd_8042762 < baseStart_8042762 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042775 : List Nat := [1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 4]
def baseStart_8042775 : Nat := 118140960795 + 8042775 * 2 ^ 59
def prefixEnd_8042775 : Nat := 4983230072969 + 3 ^ 40 * 8042775 * 2
def baseEnd_8042775 : Nat := 4129809370964875339524457

theorem tailTrace_8042775 : CollatzResearch.WordTrace tailWord_8042775 prefixEnd_8042775 4129809370964875339524457 := by
  unfold tailWord_8042775
  simp only [CollatzResearch.WordTrace]
  refine ⟨293344103437407246457497779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195562735624938164304998519 293344103437407246457497779)
  ·
    refine ⟨440016155156110869686246669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293344103437407246457497779 440016155156110869686246669)
    ·
      refine ⟨165006058183541576132342501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440016155156110869686246669 165006058183541576132342501)
      ·
        refine ⟨30938635909414045524814219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165006058183541576132342501 30938635909414045524814219)
        ·
          refine ⟨46407953864121068287221329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30938635909414045524814219 46407953864121068287221329)
          ·
            refine ⟨34805965398090801215415997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46407953864121068287221329 34805965398090801215415997)
            ·
              refine ⟨13052237024284050455780999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34805965398090801215415997 13052237024284050455780999)
              ·
                refine ⟨19578355536426075683671499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13052237024284050455780999 19578355536426075683671499)
                ·
                  refine ⟨29367533304639113525507249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19578355536426075683671499 29367533304639113525507249)
                  ·
                    refine ⟨22025649978479335144130437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29367533304639113525507249 22025649978479335144130437)
                    ·
                      refine ⟨4129809370964875339524457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22025649978479335144130437 4129809370964875339524457)
                      ·
                        rfl

theorem cell23_8042775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_8042775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042775 prefixEnd_8042775 := by exact prefixLift 8042775
  have htrace : WordTrace (prefixWord ++ tailWord_8042775) baseStart_8042775 baseEnd_8042775 := by
    simpa [prefixWord, tailWord_8042775, baseEnd_8042775] using wordTrace_append hprefix tailTrace_8042775
  have hstable : (prefixWord ++ tailWord_8042775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042775).length < 2 ^ (prefixWord ++ tailWord_8042775).sum := by decide
  have hdescent : baseEnd_8042775 < baseStart_8042775 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042812 : List Nat := [2, 2, 2, 2, 1, 2, 2, 4, 2, 1, 3]
def baseStart_8042812 : Nat := 118140960795 + 8042812 * 2 ^ 59
def prefixEnd_8042812 : Nat := 4983230072969 + 3 ^ 40 * 8042812 * 2
def baseEnd_8042812 : Nat := 4129828369749091694761787

theorem tailTrace_8042812 : CollatzResearch.WordTrace tailWord_8042812 prefixEnd_8042812 4129828369749091694761787 := by
  unfold tailWord_8042812
  simp only [CollatzResearch.WordTrace]
  refine ⟨146672726469136600888297345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195563635292182134517729793 146672726469136600888297345)
  ·
    refine ⟨110004544851852450666223009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146672726469136600888297345 110004544851852450666223009)
    ·
      refine ⟨82503408638889337999667257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110004544851852450666223009 82503408638889337999667257)
      ·
        refine ⟨61877556479167003499750443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82503408638889337999667257 61877556479167003499750443)
        ·
          refine ⟨92816334718750505249625665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61877556479167003499750443 92816334718750505249625665)
          ·
            refine ⟨69612251039062878937219249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92816334718750505249625665 69612251039062878937219249)
            ·
              refine ⟨52209188279297159202914437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69612251039062878937219249 52209188279297159202914437)
              ·
                refine ⟨9789222802368217350546457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52209188279297159202914437 9789222802368217350546457)
                ·
                  refine ⟨7341917101776163012909843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9789222802368217350546457 7341917101776163012909843)
                  ·
                    refine ⟨11012875652664244519364765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7341917101776163012909843 11012875652664244519364765)
                    ·
                      refine ⟨4129828369749091694761787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11012875652664244519364765 4129828369749091694761787)
                      ·
                        rfl

theorem cell23_8042812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_8042812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042812 prefixEnd_8042812 := by exact prefixLift 8042812
  have htrace : WordTrace (prefixWord ++ tailWord_8042812) baseStart_8042812 baseEnd_8042812 := by
    simpa [prefixWord, tailWord_8042812, baseEnd_8042812] using wordTrace_append hprefix tailTrace_8042812
  have hstable : (prefixWord ++ tailWord_8042812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042812).length < 2 ^ (prefixWord ++ tailWord_8042812).sum := by decide
  have hdescent : baseEnd_8042812 < baseStart_8042812 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042828 : List Nat := [2, 2, 1, 3, 2, 1, 2, 1, 1, 8]
def baseStart_8042828 : Nat := 118140960795 + 8042828 * 2 ^ 59
def prefixEnd_8042828 : Nat := 4983230072969 + 3 ^ 40 * 8042828 * 2
def baseEnd_8042828 : Nat := 1376612195146521210720571

theorem tailTrace_8042828 : CollatzResearch.WordTrace tailWord_8042828 prefixEnd_8042828 1376612195146521210720571 := by
  unfold tailWord_8042828
  simp only [CollatzResearch.WordTrace]
  refine ⟨146673018253107618254588569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195564024337476824339451425 146673018253107618254588569)
  ·
    refine ⟨110004763689830713690941427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146673018253107618254588569 110004763689830713690941427)
    ·
      refine ⟨165007145534746070536412141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110004763689830713690941427 165007145534746070536412141)
      ·
        refine ⟨61877679575529776451154553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165007145534746070536412141 61877679575529776451154553)
        ·
          refine ⟨46408259681647332338365915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61877679575529776451154553 46408259681647332338365915)
          ·
            refine ⟨69612389522470998507548873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46408259681647332338365915 69612389522470998507548873)
            ·
              refine ⟨52209292141853248880661655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69612389522470998507548873 52209292141853248880661655)
              ·
                refine ⟨78313938212779873320992483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52209292141853248880661655 78313938212779873320992483)
                ·
                  refine ⟨117470907319169809981488725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78313938212779873320992483 117470907319169809981488725)
                  ·
                    refine ⟨1376612195146521210720571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117470907319169809981488725 1376612195146521210720571)
                    ·
                      rfl

theorem cell23_8042828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 1, 1, 8].length) (baseStart_8042828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042828 prefixEnd_8042828 := by exact prefixLift 8042828
  have htrace : WordTrace (prefixWord ++ tailWord_8042828) baseStart_8042828 baseEnd_8042828 := by
    simpa [prefixWord, tailWord_8042828, baseEnd_8042828] using wordTrace_append hprefix tailTrace_8042828
  have hstable : (prefixWord ++ tailWord_8042828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042828).length < 2 ^ (prefixWord ++ tailWord_8042828).sum := by decide
  have hdescent : baseEnd_8042828 < baseStart_8042828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042852 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 1, 4, 2]
def baseStart_8042852 : Nat := 118140960795 + 8042852 * 2 ^ 59
def prefixEnd_8042852 : Nat := 4983230072969 + 3 ^ 40 * 8042852 * 2
def baseEnd_8042852 : Nat := 4129848908975271538261603

theorem tailTrace_8042852 : CollatzResearch.WordTrace tailWord_8042852 prefixEnd_8042852 4129848908975271538261603 := by
  unfold tailWord_8042852
  simp only [CollatzResearch.WordTrace]
  refine ⟨146673455929064144304025405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195564607905418859072033873 146673455929064144304025405)
  ·
    refine ⟨55002545973399054114009527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146673455929064144304025405 55002545973399054114009527)
    ·
      refine ⟨82503818960098581171014291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55002545973399054114009527 82503818960098581171014291)
      ·
        refine ⟨123755728440147871756521437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82503818960098581171014291 123755728440147871756521437)
        ·
          refine ⟨46408398165055451908695539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123755728440147871756521437 46408398165055451908695539)
          ·
            refine ⟨69612597247583177863043309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46408398165055451908695539 69612597247583177863043309)
            ·
              refine ⟨26104723967843691698641241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69612597247583177863043309 26104723967843691698641241)
              ·
                refine ⟨19578542975882768773980931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26104723967843691698641241 19578542975882768773980931)
                ·
                  refine ⟨29367814463824153160971397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19578542975882768773980931 29367814463824153160971397)
                  ·
                    refine ⟨5506465211967028717682137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29367814463824153160971397 5506465211967028717682137)
                    ·
                      refine ⟨4129848908975271538261603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506465211967028717682137 4129848908975271538261603)
                      ·
                        rfl

theorem cell23_8042852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 1, 4, 2].length) (baseStart_8042852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042852 prefixEnd_8042852 := by exact prefixLift 8042852
  have htrace : WordTrace (prefixWord ++ tailWord_8042852) baseStart_8042852 baseEnd_8042852 := by
    simpa [prefixWord, tailWord_8042852, baseEnd_8042852] using wordTrace_append hprefix tailTrace_8042852
  have hstable : (prefixWord ++ tailWord_8042852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042852).length < 2 ^ (prefixWord ++ tailWord_8042852).sum := by decide
  have hdescent : baseEnd_8042852 < baseStart_8042852 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042855 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_8042855 : Nat := 118140960795 + 8042855 * 2 ^ 59
def prefixEnd_8042855 : Nat := 4983230072969 + 3 ^ 40 * 8042855 * 2
def baseEnd_8042855 : Nat := 4129850449417235026524089

theorem tailTrace_8042855 : CollatzResearch.WordTrace tailWord_8042855 prefixEnd_8042855 4129850449417235026524089 := by
  unfold tailWord_8042855
  simp only [CollatzResearch.WordTrace]
  refine ⟨293347021277117420120410019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195564680851411613413606679 293347021277117420120410019)
  ·
    refine ⟨440020531915676130180615029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293347021277117420120410019 440020531915676130180615029)
    ·
      refine ⟨41251924867094637204432659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 440020531915676130180615029 41251924867094637204432659)
      ·
        refine ⟨61877887300641955806648989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41251924867094637204432659 61877887300641955806648989)
        ·
          refine ⟨23204207737740733427493371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61877887300641955806648989 23204207737740733427493371)
          ·
            refine ⟨34806311606611100141240057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23204207737740733427493371 34806311606611100141240057)
            ·
              refine ⟨26104733704958325105930043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34806311606611100141240057 26104733704958325105930043)
              ·
                refine ⟨39157100557437487658895065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26104733704958325105930043 39157100557437487658895065)
                ·
                  refine ⟨29367825418078115744171299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39157100557437487658895065 29367825418078115744171299)
                  ·
                    refine ⟨44051738127117173616256949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29367825418078115744171299 44051738127117173616256949)
                    ·
                      refine ⟨4129850449417235026524089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44051738127117173616256949 4129850449417235026524089)
                      ·
                        rfl

theorem cell23_8042855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_8042855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042855 prefixEnd_8042855 := by exact prefixLift 8042855
  have htrace : WordTrace (prefixWord ++ tailWord_8042855) baseStart_8042855 baseEnd_8042855 := by
    simpa [prefixWord, tailWord_8042855, baseEnd_8042855] using wordTrace_append hprefix tailTrace_8042855
  have hstable : (prefixWord ++ tailWord_8042855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042855).length < 2 ^ (prefixWord ++ tailWord_8042855).sum := by decide
  have hdescent : baseEnd_8042855 < baseStart_8042855 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042856 : List Nat := [2, 1, 4, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_8042856 : Nat := 118140960795 + 8042856 * 2 ^ 59
def prefixEnd_8042856 : Nat := 4983230072969 + 3 ^ 40 * 8042856 * 2
def baseEnd_8042856 : Nat := 4129850962897889522611585

theorem tailTrace_8042856 : CollatzResearch.WordTrace tailWord_8042856 prefixEnd_8042856 4129850962897889522611585 := by
  unfold tailWord_8042856
  simp only [CollatzResearch.WordTrace]
  refine ⟨146673528875056898645598211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195564705166742531527464281 146673528875056898645598211)
  ·
    refine ⟨220010293312585347968397317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146673528875056898645598211 220010293312585347968397317)
    ·
      refine ⟨41251929996109752744074497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220010293312585347968397317 41251929996109752744074497)
      ·
        refine ⟨30938947497082314558055873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41251929996109752744074497 30938947497082314558055873)
        ·
          refine ⟨23204210622811735918541905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30938947497082314558055873 23204210622811735918541905)
          ·
            refine ⟨17403157967108801938906429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23204210622811735918541905 17403157967108801938906429)
            ·
              refine ⟨6526184237665800727089911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17403157967108801938906429 6526184237665800727089911)
              ·
                refine ⟨9789276356498701090634867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526184237665800727089911 9789276356498701090634867)
                ·
                  refine ⟨14683914534748051635952301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9789276356498701090634867 14683914534748051635952301)
                  ·
                    refine ⟨5506467950530519363482113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14683914534748051635952301 5506467950530519363482113)
                    ·
                      refine ⟨4129850962897889522611585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506467950530519363482113 4129850962897889522611585)
                      ·
                        rfl

theorem cell23_8042856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_8042856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042856 prefixEnd_8042856 := by exact prefixLift 8042856
  have htrace : WordTrace (prefixWord ++ tailWord_8042856) baseStart_8042856 baseEnd_8042856 := by
    simpa [prefixWord, tailWord_8042856, baseEnd_8042856] using wordTrace_append hprefix tailTrace_8042856
  have hstable : (prefixWord ++ tailWord_8042856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042856).length < 2 ^ (prefixWord ++ tailWord_8042856).sum := by decide
  have hdescent : baseEnd_8042856 < baseStart_8042856 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042909 : List Nat := [1, 4, 2, 1, 4, 1, 2, 3, 5]
def baseStart_8042909 : Nat := 118140960795 + 8042909 * 2 ^ 59
def prefixEnd_8042909 : Nat := 4983230072969 + 3 ^ 40 * 8042909 * 2
def baseEnd_8042909 : Nat := 458875353041397535027649

theorem tailTrace_8042909 : CollatzResearch.WordTrace tailWord_8042909 prefixEnd_8042909 458875353041397535027649 := by
  unfold tailWord_8042909
  simp only [CollatzResearch.WordTrace]
  refine ⟨293348990818921787342875781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195565993879281191561917187 293348990818921787342875781)
  ·
    refine ⟨55002935778547835126789209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293348990818921787342875781 55002935778547835126789209)
    ·
      refine ⟨41252201833910876345091907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55002935778547835126789209 41252201833910876345091907)
      ·
        refine ⟨61878302750866314517637861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41252201833910876345091907 61878302750866314517637861)
        ·
          refine ⟨11602181765787433972057099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61878302750866314517637861 11602181765787433972057099)
          ·
            refine ⟨17403272648681150958085649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11602181765787433972057099 17403272648681150958085649)
            ·
              refine ⟨13052454486510863218564237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17403272648681150958085649 13052454486510863218564237)
              ·
                refine ⟨4894670432441573706961589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13052454486510863218564237 4894670432441573706961589)
                ·
                  refine ⟨458875353041397535027649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4894670432441573706961589 458875353041397535027649)
                  ·
                    rfl

theorem cell23_8042909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 2, 3, 5].length) (baseStart_8042909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042909 prefixEnd_8042909 := by exact prefixLift 8042909
  have htrace : WordTrace (prefixWord ++ tailWord_8042909) baseStart_8042909 baseEnd_8042909 := by
    simpa [prefixWord, tailWord_8042909, baseEnd_8042909] using wordTrace_append hprefix tailTrace_8042909
  have hstable : (prefixWord ++ tailWord_8042909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042909).length < 2 ^ (prefixWord ++ tailWord_8042909).sum := by decide
  have hdescent : baseEnd_8042909 < baseStart_8042909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042952 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 3, 4]
def baseStart_8042952 : Nat := 118140960795 + 8042952 * 2 ^ 59
def prefixEnd_8042952 : Nat := 4983230072969 + 3 ^ 40 * 8042952 * 2
def baseEnd_8042952 : Nat := 1376633419013573715670381

theorem tailTrace_8042952 : CollatzResearch.WordTrace tailWord_8042952 prefixEnd_8042952 1376633419013573715670381 := by
  unfold tailWord_8042952
  simp only [CollatzResearch.WordTrace]
  refine ⟨146675279578883002843345555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195567039438510670457794073 146675279578883002843345555)
  ·
    refine ⟨220012919368324504265018333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146675279578883002843345555 220012919368324504265018333)
    ·
      refine ⟨82504844763121689099381875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220012919368324504265018333 82504844763121689099381875)
      ·
        refine ⟨123757267144682533649072813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82504844763121689099381875 123757267144682533649072813)
        ·
          refine ⟨46408975179255950118402305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123757267144682533649072813 46408975179255950118402305)
          ·
            refine ⟨34806731384441962588801729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46408975179255950118402305 34806731384441962588801729)
            ·
              refine ⟨26105048538331471941601297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34806731384441962588801729 26105048538331471941601297)
              ·
                refine ⟨19578786403748603956200973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26105048538331471941601297 19578786403748603956200973)
                ·
                  refine ⟨7342044901405726483575365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19578786403748603956200973 7342044901405726483575365)
                  ·
                    refine ⟨1376633419013573715670381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7342044901405726483575365 1376633419013573715670381)
                    ·
                      rfl

theorem cell23_8042952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_8042952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042952 prefixEnd_8042952 := by exact prefixLift 8042952
  have htrace : WordTrace (prefixWord ++ tailWord_8042952) baseStart_8042952 baseEnd_8042952 := by
    simpa [prefixWord, tailWord_8042952, baseEnd_8042952] using wordTrace_append hprefix tailTrace_8042952
  have hstable : (prefixWord ++ tailWord_8042952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042952).length < 2 ^ (prefixWord ++ tailWord_8042952).sum := by decide
  have hdescent : baseEnd_8042952 < baseStart_8042952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042965 : List Nat := [1, 3, 2, 3, 1, 2, 1, 2, 8]
def baseStart_8042965 : Nat := 118140960795 + 8042965 * 2 ^ 59
def prefixEnd_8042965 : Nat := 4983230072969 + 3 ^ 40 * 8042965 * 2
def baseEnd_8042965 : Nat := 458878548032136621794287

theorem tailTrace_8042965 : CollatzResearch.WordTrace tailWord_8042965 prefixEnd_8042965 458878548032136621794287 := by
  unfold tailWord_8042965
  simp only [CollatzResearch.WordTrace]
  refine ⟨293351033306718908906914349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195567355537812605937942899 293351033306718908906914349)
  ·
    refine ⟨110006637490019590840092881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293351033306718908906914349 110006637490019590840092881)
    ·
      refine ⟨82504978117514693130069661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110006637490019590840092881 82504978117514693130069661)
      ·
        refine ⟨30939366794068009923776123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82504978117514693130069661 30939366794068009923776123)
        ·
          refine ⟨46409050191102014885664185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30939366794068009923776123 46409050191102014885664185)
          ·
            refine ⟨34806787643326511164248139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46409050191102014885664185 34806787643326511164248139)
            ·
              refine ⟨52210181464989766746372209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34806787643326511164248139 52210181464989766746372209)
              ·
                refine ⟨39157636098742325059779157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52210181464989766746372209 39157636098742325059779157)
                ·
                  refine ⟨458878548032136621794287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39157636098742325059779157 458878548032136621794287)
                  ·
                    rfl

theorem cell23_8042965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 1, 2, 8].length) (baseStart_8042965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042965 prefixEnd_8042965 := by exact prefixLift 8042965
  have htrace : WordTrace (prefixWord ++ tailWord_8042965) baseStart_8042965 baseEnd_8042965 := by
    simpa [prefixWord, tailWord_8042965, baseEnd_8042965] using wordTrace_append hprefix tailTrace_8042965
  have hstable : (prefixWord ++ tailWord_8042965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042965).length < 2 ^ (prefixWord ++ tailWord_8042965).sum := by decide
  have hdescent : baseEnd_8042965 < baseStart_8042965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042979 : List Nat := [1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 3]
def baseStart_8042979 : Nat := 118140960795 + 8042979 * 2 ^ 59
def prefixEnd_8042979 : Nat := 4983230072969 + 3 ^ 40 * 8042979 * 2
def baseEnd_8042979 : Nat := 4129914121018392541373519

theorem tailTrace_8042979 : CollatzResearch.WordTrace tailWord_8042979 prefixEnd_8042979 4129914121018392541373519 := by
  unfold tailWord_8042979
  simp only [CollatzResearch.WordTrace]
  refine ⟨293351543928668189297923991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195567695952445459531949327 293351543928668189297923991)
  ·
    refine ⟨440027315893002283946885987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293351543928668189297923991 440027315893002283946885987)
    ·
      refine ⟨660040973839503425920328981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440027315893002283946885987 660040973839503425920328981)
      ·
        refine ⟨30939420648726723090015421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 660040973839503425920328981 30939420648726723090015421)
        ·
          refine ⟨11602282743272521158755783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30939420648726723090015421 11602282743272521158755783)
          ·
            refine ⟨17403424114908781738133675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11602282743272521158755783 17403424114908781738133675)
            ·
              refine ⟨26105136172363172607200513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17403424114908781738133675 26105136172363172607200513)
              ·
                refine ⟨19578852129272379455400385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26105136172363172607200513 19578852129272379455400385)
                ·
                  refine ⟨14684139096954284591550289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19578852129272379455400385 14684139096954284591550289)
                  ·
                    refine ⟨11013104322715713443662717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14684139096954284591550289 11013104322715713443662717)
                    ·
                      refine ⟨4129914121018392541373519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11013104322715713443662717 4129914121018392541373519)
                      ·
                        rfl

theorem cell23_8042979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_8042979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042979 prefixEnd_8042979 := by exact prefixLift 8042979
  have htrace : WordTrace (prefixWord ++ tailWord_8042979) baseStart_8042979 baseEnd_8042979 := by
    simpa [prefixWord, tailWord_8042979, baseEnd_8042979] using wordTrace_append hprefix tailTrace_8042979
  have hstable : (prefixWord ++ tailWord_8042979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042979).length < 2 ^ (prefixWord ++ tailWord_8042979).sum := by decide
  have hdescent : baseEnd_8042979 < baseStart_8042979 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8042995 : List Nat := [1, 1, 1, 2, 2, 2, 4, 2, 3, 5]
def baseStart_8042995 : Nat := 118140960795 + 8042995 * 2 ^ 59
def prefixEnd_8042995 : Nat := 4983230072969 + 3 ^ 40 * 8042995 * 2
def baseEnd_8042995 : Nat := 1376640778902954826257815

theorem tailTrace_8042995 : CollatzResearch.WordTrace tailWord_8042995 prefixEnd_8042995 1376640778902954826257815 := by
  unfold tailWord_8042995
  simp only [CollatzResearch.WordTrace]
  refine ⟨293352127496610224030506439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195568084997740149353670959 293352127496610224030506439)
  ·
    refine ⟨440028191244915336045759659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293352127496610224030506439 440028191244915336045759659)
    ·
      refine ⟨660042286867373004068639489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440028191244915336045759659 660042286867373004068639489)
      ·
        refine ⟨495031715150529753051479617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660042286867373004068639489 495031715150529753051479617)
        ·
          refine ⟨371273786362897314788609713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495031715150529753051479617 371273786362897314788609713)
          ·
            refine ⟨278455339772172986091457285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371273786362897314788609713 278455339772172986091457285)
            ·
              refine ⟨52210376207282434892148241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278455339772172986091457285 52210376207282434892148241)
              ·
                refine ⟨39157782155461826169111181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52210376207282434892148241 39157782155461826169111181)
                ·
                  refine ⟨14684168308298184813416693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39157782155461826169111181 14684168308298184813416693)
                  ·
                    refine ⟨1376640778902954826257815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14684168308298184813416693 1376640778902954826257815)
                    ·
                      rfl

theorem cell23_8042995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 2, 3, 5].length) (baseStart_8042995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8042995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8042995 prefixEnd_8042995 := by exact prefixLift 8042995
  have htrace : WordTrace (prefixWord ++ tailWord_8042995) baseStart_8042995 baseEnd_8042995 := by
    simpa [prefixWord, tailWord_8042995, baseEnd_8042995] using wordTrace_append hprefix tailTrace_8042995
  have hstable : (prefixWord ++ tailWord_8042995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8042995).length < 2 ^ (prefixWord ++ tailWord_8042995).sum := by decide
  have hdescent : baseEnd_8042995 < baseStart_8042995 := by decide
  rcases family_descends (prefixWord ++ tailWord_8042995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043002 : List Nat := [3, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2]
def baseStart_8043002 : Nat := 118140960795 + 8043002 * 2 ^ 59
def prefixEnd_8043002 : Nat := 4983230072969 + 3 ^ 40 * 8043002 * 2
def baseEnd_8043002 : Nat := 4129925931073445951385913

theorem tailTrace_8043002 : CollatzResearch.WordTrace tailWord_8043002 prefixEnd_8043002 4129925931073445951385913 := by
  unfold tailWord_8043002
  simp only [CollatzResearch.WordTrace]
  refine ⟨73338095701896216056502815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195568255205056576150674173 73338095701896216056502815)
  ·
    refine ⟨110007143552844324084754223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73338095701896216056502815 110007143552844324084754223)
    ·
      refine ⟨165010715329266486127131335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110007143552844324084754223 165010715329266486127131335)
      ·
        refine ⟨247516072993899729190697003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165010715329266486127131335 247516072993899729190697003)
        ·
          refine ⟨371274109490849593786045505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247516072993899729190697003 371274109490849593786045505)
          ·
            refine ⟨278455582118137195339534129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371274109490849593786045505 278455582118137195339534129)
            ·
              refine ⟨208841686588602896504650597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278455582118137195339534129 208841686588602896504650597)
              ·
                refine ⟨39157816235363043094621987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208841686588602896504650597 39157816235363043094621987)
                ·
                  refine ⟨58736724353044564641932981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39157816235363043094621987 58736724353044564641932981)
                  ·
                    refine ⟨5506567908097927935181217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58736724353044564641932981 5506567908097927935181217)
                    ·
                      refine ⟨4129925931073445951385913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506567908097927935181217 4129925931073445951385913)
                      ·
                        rfl

theorem cell23_8043002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 4, 1, 5, 2].length) (baseStart_8043002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043002 prefixEnd_8043002 := by exact prefixLift 8043002
  have htrace : WordTrace (prefixWord ++ tailWord_8043002) baseStart_8043002 baseEnd_8043002 := by
    simpa [prefixWord, tailWord_8043002, baseEnd_8043002] using wordTrace_append hprefix tailTrace_8043002
  have hstable : (prefixWord ++ tailWord_8043002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043002).length < 2 ^ (prefixWord ++ tailWord_8043002).sum := by decide
  have hdescent : baseEnd_8043002 < baseStart_8043002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043019 : List Nat := [1, 1, 1, 1, 7, 1, 1, 3, 2, 3, 2]
def baseStart_8043019 : Nat := 118140960795 + 8043019 * 2 ^ 59
def prefixEnd_8043019 : Nat := 4983230072969 + 3 ^ 40 * 8043019 * 2
def baseEnd_8043019 : Nat := 4129934660244572384873335

theorem tailTrace_8043019 : CollatzResearch.WordTrace tailWord_8043019 prefixEnd_8043019 4129934660244572384873335 := by
  unfold tailWord_8043019
  simp only [CollatzResearch.WordTrace]
  refine ⟨293353002848523276129380111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195568668565682184086253407 293353002848523276129380111)
  ·
    refine ⟨440029504272784914194070167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293353002848523276129380111 440029504272784914194070167)
    ·
      refine ⟨660044256409177371291105251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440029504272784914194070167 660044256409177371291105251)
      ·
        refine ⟨990066384613766056936657877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660044256409177371291105251 990066384613766056936657877)
        ·
          refine ⟨23204680889385141959452919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 990066384613766056936657877 23204680889385141959452919)
          ·
            refine ⟨34807021334077712939179379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23204680889385141959452919 34807021334077712939179379)
            ·
              refine ⟨52210532001116569408769069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34807021334077712939179379 52210532001116569408769069)
              ·
                refine ⟨19578949500418713528288401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52210532001116569408769069 19578949500418713528288401)
                ·
                  refine ⟨14684212125314035146216301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19578949500418713528288401 14684212125314035146216301)
                  ·
                    refine ⟨5506579546992763179831113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14684212125314035146216301 5506579546992763179831113)
                    ·
                      refine ⟨4129934660244572384873335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506579546992763179831113 4129934660244572384873335)
                      ·
                        rfl

theorem cell23_8043019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 3, 2].length) (baseStart_8043019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043019 prefixEnd_8043019 := by exact prefixLift 8043019
  have htrace : WordTrace (prefixWord ++ tailWord_8043019) baseStart_8043019 baseEnd_8043019 := by
    simpa [prefixWord, tailWord_8043019, baseEnd_8043019] using wordTrace_append hprefix tailTrace_8043019
  have hstable : (prefixWord ++ tailWord_8043019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043019).length < 2 ^ (prefixWord ++ tailWord_8043019).sum := by decide
  have hdescent : baseEnd_8043019 < baseStart_8043019 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043029 : List Nat := [1, 3, 2, 1, 3, 1, 5, 1, 1, 5]
def baseStart_8043029 : Nat := 118140960795 + 8043029 * 2 ^ 59
def prefixEnd_8043029 : Nat := 4983230072969 + 3 ^ 40 * 8043029 * 2
def baseEnd_8043029 : Nat := 1376646598350372448582763

theorem tailTrace_8043029 : CollatzResearch.WordTrace tailWord_8043029 prefixEnd_8043029 1376646598350372448582763 := by
  unfold tailWord_8043029
  simp only [CollatzResearch.WordTrace]
  refine ⟨293353367578487047837244141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195568911718991365224829427 293353367578487047837244141)
  ·
    refine ⟨110007512841932642938966553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293353367578487047837244141 110007512841932642938966553)
    ·
      refine ⟨82505634631449482204224915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110007512841932642938966553 82505634631449482204224915)
      ·
        refine ⟨123758451947174223306337373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82505634631449482204224915 123758451947174223306337373)
        ·
          refine ⟨46409419480190333739876515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123758451947174223306337373 46409419480190333739876515)
          ·
            refine ⟨69614129220285500609814773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46409419480190333739876515 69614129220285500609814773)
            ·
              refine ⟨6526324614401765682170135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69614129220285500609814773 6526324614401765682170135)
              ·
                refine ⟨9789486921602648523255203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526324614401765682170135 9789486921602648523255203)
                ·
                  refine ⟨14684230382403972784882805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9789486921602648523255203 14684230382403972784882805)
                  ·
                    refine ⟨1376646598350372448582763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14684230382403972784882805 1376646598350372448582763)
                    ·
                      rfl

theorem cell23_8043029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_8043029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043029 prefixEnd_8043029 := by exact prefixLift 8043029
  have htrace : WordTrace (prefixWord ++ tailWord_8043029) baseStart_8043029 baseEnd_8043029 := by
    simpa [prefixWord, tailWord_8043029, baseEnd_8043029] using wordTrace_append hprefix tailTrace_8043029
  have hstable : (prefixWord ++ tailWord_8043029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043029).length < 2 ^ (prefixWord ++ tailWord_8043029).sum := by decide
  have hdescent : baseEnd_8043029 < baseStart_8043029 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043043 : List Nat := [1, 1, 1, 4, 4, 1, 4, 2, 1, 1, 3]
def baseStart_8043043 : Nat := 118140960795 + 8043043 * 2 ^ 59
def prefixEnd_8043043 : Nat := 4983230072969 + 3 ^ 40 * 8043043 * 2
def baseEnd_8043043 : Nat := 4129946983780280290973225

theorem tailTrace_8043043 : CollatzResearch.WordTrace tailWord_8043043 prefixEnd_8043043 4129946983780280290973225 := by
  unfold tailWord_8043043
  simp only [CollatzResearch.WordTrace]
  refine ⟨293353878200436328228253783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195569252133624218818835855 293353878200436328228253783)
  ·
    refine ⟨440030817300654492342380675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293353878200436328228253783 440030817300654492342380675)
    ·
      refine ⟨660046225950981738513571013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440030817300654492342380675 660046225950981738513571013)
      ·
        refine ⟨123758667365809075971294565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 660046225950981738513571013 123758667365809075971294565)
        ·
          refine ⟨23204750131089201744617731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 123758667365809075971294565 23204750131089201744617731)
          ·
            refine ⟨34807125196633802616926597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23204750131089201744617731 34807125196633802616926597)
            ·
              refine ⟨6526335974368837990673737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34807125196633802616926597 6526335974368837990673737)
              ·
                refine ⟨4894751980776628493005303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6526335974368837990673737 4894751980776628493005303)
                ·
                  refine ⟨7342127971164942739507955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4894751980776628493005303 7342127971164942739507955)
                  ·
                    refine ⟨11013191956747414109261933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7342127971164942739507955 11013191956747414109261933)
                    ·
                      refine ⟨4129946983780280290973225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11013191956747414109261933 4129946983780280290973225)
                      ·
                        rfl

theorem cell23_8043043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_8043043 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043043 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043043 prefixEnd_8043043 := by exact prefixLift 8043043
  have htrace : WordTrace (prefixWord ++ tailWord_8043043) baseStart_8043043 baseEnd_8043043 := by
    simpa [prefixWord, tailWord_8043043, baseEnd_8043043] using wordTrace_append hprefix tailTrace_8043043
  have hstable : (prefixWord ++ tailWord_8043043).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043043).length < 2 ^ (prefixWord ++ tailWord_8043043).sum := by decide
  have hdescent : baseEnd_8043043 < baseStart_8043043 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043045 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 6]
def baseStart_8043045 : Nat := 118140960795 + 8043045 * 2 ^ 59
def prefixEnd_8043045 : Nat := 4983230072969 + 3 ^ 40 * 8043045 * 2
def baseEnd_8043045 : Nat := 4129948010741589283148215

theorem tailTrace_8043045 : CollatzResearch.WordTrace tailWord_8043045 prefixEnd_8043045 4129948010741589283148215 := by
  unfold tailWord_8043045
  simp only [CollatzResearch.WordTrace]
  refine ⟨293353951146429082569826589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195569300764286055046551059 293353951146429082569826589)
  ·
    refine ⟨110007731679910905963684971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293353951146429082569826589 110007731679910905963684971)
    ·
      refine ⟨165011597519866358945527457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110007731679910905963684971 165011597519866358945527457)
      ·
        refine ⟨123758698139899769209145593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165011597519866358945527457 123758698139899769209145593)
        ·
          refine ⟨92819023604924826906859195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123758698139899769209145593 92819023604924826906859195)
          ·
            refine ⟨139228535407387240360288793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92819023604924826906859195 139228535407387240360288793)
            ·
              refine ⟨104421401555540430270216595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139228535407387240360288793 104421401555540430270216595)
              ·
                refine ⟨156632102333310645405324893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104421401555540430270216595 156632102333310645405324893)
                ·
                  refine ⟨58737038374991492026996835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156632102333310645405324893 58737038374991492026996835)
                  ·
                    refine ⟨88105557562487238040495253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58737038374991492026996835 88105557562487238040495253)
                    ·
                      refine ⟨4129948010741589283148215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88105557562487238040495253 4129948010741589283148215)
                      ·
                        rfl

theorem cell23_8043045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 1, 6].length) (baseStart_8043045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043045 prefixEnd_8043045 := by exact prefixLift 8043045
  have htrace : WordTrace (prefixWord ++ tailWord_8043045) baseStart_8043045 baseEnd_8043045 := by
    simpa [prefixWord, tailWord_8043045, baseEnd_8043045] using wordTrace_append hprefix tailTrace_8043045
  have hstable : (prefixWord ++ tailWord_8043045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043045).length < 2 ^ (prefixWord ++ tailWord_8043045).sum := by decide
  have hdescent : baseEnd_8043045 < baseStart_8043045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043066 : List Nat := [3, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2]
def baseStart_8043066 : Nat := 118140960795 + 8043066 * 2 ^ 59
def prefixEnd_8043066 : Nat := 4983230072969 + 3 ^ 40 * 8043066 * 2
def baseEnd_8043066 : Nat := 4129958793835333700985619

theorem tailTrace_8043066 : CollatzResearch.WordTrace tailWord_8043066 prefixEnd_8043066 4129958793835333700985619 := by
  unfold tailWord_8043066
  simp only [CollatzResearch.WordTrace]
  refine ⟨73338679269838250789085263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195569811386235335437560701 73338679269838250789085263)
  ·
    refine ⟨110008018904757376183627895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73338679269838250789085263 110008018904757376183627895)
    ·
      refine ⟨165012028357136064275441843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110008018904757376183627895 165012028357136064275441843)
      ·
        refine ⟨247518042535704096413162765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165012028357136064275441843 247518042535704096413162765)
        ·
          refine ⟨92819265950889036154936037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247518042535704096413162765 92819265950889036154936037)
          ·
            refine ⟨17403612365791694279050507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92819265950889036154936037 17403612365791694279050507)
            ·
              refine ⟨26105418548687541418575761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17403612365791694279050507 26105418548687541418575761)
              ·
                refine ⟨19579063911515656063931821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26105418548687541418575761 19579063911515656063931821)
                ·
                  refine ⟨7342148966818371023974433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19579063911515656063931821 7342148966818371023974433)
                  ·
                    refine ⟨5506611725113778267980825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7342148966818371023974433 5506611725113778267980825)
                    ·
                      refine ⟨4129958793835333700985619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506611725113778267980825 4129958793835333700985619)
                      ·
                        rfl

theorem cell23_8043066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 2, 3, 2, 2].length) (baseStart_8043066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043066 prefixEnd_8043066 := by exact prefixLift 8043066
  have htrace : WordTrace (prefixWord ++ tailWord_8043066) baseStart_8043066 baseEnd_8043066 := by
    simpa [prefixWord, tailWord_8043066, baseEnd_8043066] using wordTrace_append hprefix tailTrace_8043066
  have hstable : (prefixWord ++ tailWord_8043066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043066).length < 2 ^ (prefixWord ++ tailWord_8043066).sum := by decide
  have hdescent : baseEnd_8043066 < baseStart_8043066 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043069 : List Nat := [1, 4, 1, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_8043069 : Nat := 118140960795 + 8043069 * 2 ^ 59
def prefixEnd_8043069 : Nat := 4983230072969 + 3 ^ 40 * 8043069 * 2
def baseEnd_8043069 : Nat := 4129960334277297189248105

theorem tailTrace_8043069 : CollatzResearch.WordTrace tailWord_8043069 prefixEnd_8043069 4129960334277297189248105 := by
  unfold tailWord_8043069
  simp only [CollatzResearch.WordTrace]
  refine ⟨293354826498342134668700261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195569884332228089779133507 293354826498342134668700261)
  ·
    refine ⟨55004029968439150250381299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293354826498342134668700261 55004029968439150250381299)
    ·
      refine ⟨82506044952658725375571949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55004029968439150250381299 82506044952658725375571949)
      ·
        refine ⟨30939766857247022015839481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82506044952658725375571949 30939766857247022015839481)
        ·
          refine ⟨23204825142935266511879611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30939766857247022015839481 23204825142935266511879611)
          ·
            refine ⟨34807237714402899767819417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23204825142935266511879611 34807237714402899767819417)
            ·
              refine ⟨26105428285802174825864563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34807237714402899767819417 26105428285802174825864563)
              ·
                refine ⟨39158142428703262238796845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26105428285802174825864563 39158142428703262238796845)
                ·
                  refine ⟨14684303410763723339548817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39158142428703262238796845 14684303410763723339548817)
                  ·
                    refine ⟨11013227558072792504661613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14684303410763723339548817 11013227558072792504661613)
                    ·
                      refine ⟨4129960334277297189248105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11013227558072792504661613 4129960334277297189248105)
                      ·
                        rfl

theorem cell23_8043069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_8043069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043069 prefixEnd_8043069 := by exact prefixLift 8043069
  have htrace : WordTrace (prefixWord ++ tailWord_8043069) baseStart_8043069 baseEnd_8043069 := by
    simpa [prefixWord, tailWord_8043069, baseEnd_8043069] using wordTrace_append hprefix tailTrace_8043069
  have hstable : (prefixWord ++ tailWord_8043069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043069).length < 2 ^ (prefixWord ++ tailWord_8043069).sum := by decide
  have hdescent : baseEnd_8043069 < baseStart_8043069 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043070 : List Nat := [4, 2, 1, 4, 1, 2, 1, 1, 2, 3, 2]
def baseStart_8043070 : Nat := 118140960795 + 8043070 * 2 ^ 59
def prefixEnd_8043070 : Nat := 4983230072969 + 3 ^ 40 * 8043070 * 2
def baseEnd_8043070 : Nat := 4129960847757951685335601

theorem tailTrace_8043070 : CollatzResearch.WordTrace tailWord_8043070 prefixEnd_8043070 4129960847757951685335601 := by
  unfold tailWord_8043070
  simp only [CollatzResearch.WordTrace]
  refine ⟨36669357871417313979935833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195569908647559007892991109 36669357871417313979935833)
  ·
    refine ⟨27502018403562985484951875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36669357871417313979935833 27502018403562985484951875)
    ·
      refine ⟨41253027605344478227427813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27502018403562985484951875 41253027605344478227427813)
      ·
        refine ⟨7734942676002089667642715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41253027605344478227427813 7734942676002089667642715)
        ·
          refine ⟨11602414014003134501464073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734942676002089667642715 11602414014003134501464073)
          ·
            refine ⟨8701810510502350876098055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11602414014003134501464073 8701810510502350876098055)
            ·
              refine ⟨13052715765753526314147083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8701810510502350876098055 13052715765753526314147083)
              ·
                refine ⟨19579073648630289471220625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13052715765753526314147083 19579073648630289471220625)
                ·
                  refine ⟨14684305236472717103415469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19579073648630289471220625 14684305236472717103415469)
                  ·
                    refine ⟨5506614463677268913780801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14684305236472717103415469 5506614463677268913780801)
                    ·
                      refine ⟨4129960847757951685335601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506614463677268913780801 4129960847757951685335601)
                      ·
                        rfl

theorem cell23_8043070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_8043070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043070 prefixEnd_8043070 := by exact prefixLift 8043070
  have htrace : WordTrace (prefixWord ++ tailWord_8043070) baseStart_8043070 baseEnd_8043070 := by
    simpa [prefixWord, tailWord_8043070, baseEnd_8043070] using wordTrace_append hprefix tailTrace_8043070
  have hstable : (prefixWord ++ tailWord_8043070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043070).length < 2 ^ (prefixWord ++ tailWord_8043070).sum := by decide
  have hdescent : baseEnd_8043070 < baseStart_8043070 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043086 : List Nat := [4, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3]
def baseStart_8043086 : Nat := 118140960795 + 8043086 * 2 ^ 59
def prefixEnd_8043086 : Nat := 4983230072969 + 3 ^ 40 * 8043086 * 2
def baseEnd_8043086 : Nat := 4129969063448423622735527

theorem tailTrace_8043086 : CollatzResearch.WordTrace tailWord_8043086 prefixEnd_8043086 4129969063448423622735527 := by
  unfold tailWord_8043086
  simp only [CollatzResearch.WordTrace]
  refine ⟨36669430817410068321508639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195570297692853697714712741 36669430817410068321508639)
  ·
    refine ⟨55004146226115102482262959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36669430817410068321508639 55004146226115102482262959)
    ·
      refine ⟨82506219339172653723394439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55004146226115102482262959 82506219339172653723394439)
      ·
        refine ⟨123759329008758980585091659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82506219339172653723394439 123759329008758980585091659)
        ·
          refine ⟨185638993513138470877637489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123759329008758980585091659 185638993513138470877637489)
          ·
            refine ⟨139229245134853853158228117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185638993513138470877637489 139229245134853853158228117)
            ·
              refine ⟨6526370865696274366791943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139229245134853853158228117 6526370865696274366791943)
              ·
                refine ⟨9789556298544411550187915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526370865696274366791943 9789556298544411550187915)
                ·
                  refine ⟨14684334447816617325281873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9789556298544411550187915 14684334447816617325281873)
                  ·
                    refine ⟨11013250835862462993961405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14684334447816617325281873 11013250835862462993961405)
                    ·
                      refine ⟨4129969063448423622735527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11013250835862462993961405 4129969063448423622735527)
                      ·
                        rfl

theorem cell23_8043086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_8043086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043086 prefixEnd_8043086 := by exact prefixLift 8043086
  have htrace : WordTrace (prefixWord ++ tailWord_8043086) baseStart_8043086 baseEnd_8043086 := by
    simpa [prefixWord, tailWord_8043086, baseEnd_8043086] using wordTrace_append hprefix tailTrace_8043086
  have hstable : (prefixWord ++ tailWord_8043086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043086).length < 2 ^ (prefixWord ++ tailWord_8043086).sum := by decide
  have hdescent : baseEnd_8043086 < baseStart_8043086 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043115 : List Nat := [1, 1, 1, 1, 2, 2, 1, 5, 1, 8]
def baseStart_8043115 : Nat := 118140960795 + 8043115 * 2 ^ 59
def prefixEnd_8043115 : Nat := 4983230072969 + 3 ^ 40 * 8043115 * 2
def baseEnd_8043115 : Nat := 1376661318129134669757631

theorem tailTrace_8043115 : CollatzResearch.WordTrace tailWord_8043115 prefixEnd_8043115 1376661318129134669757631 := by
  unfold tailWord_8043115
  simp only [CollatzResearch.WordTrace]
  refine ⟨293356504256175484524874799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195571002837450323016583199 293356504256175484524874799)
  ·
    refine ⟨440034756384263226787312199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293356504256175484524874799 440034756384263226787312199)
    ·
      refine ⟨660052134576394840180968299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440034756384263226787312199 660052134576394840180968299)
      ·
        refine ⟨990078201864592260271452449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660052134576394840180968299 990078201864592260271452449)
        ·
          refine ⟨742558651398444195203589337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990078201864592260271452449 742558651398444195203589337)
          ·
            refine ⟨556918988548833146402692003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742558651398444195203589337 556918988548833146402692003)
            ·
              refine ⟨835378482823249719604038005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556918988548833146402692003 835378482823249719604038005)
              ·
                refine ⟨78316732764679661212878563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 835378482823249719604038005 78316732764679661212878563)
                ·
                  refine ⟨117475099147019491819317845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78316732764679661212878563 117475099147019491819317845)
                  ·
                    refine ⟨1376661318129134669757631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117475099147019491819317845 1376661318129134669757631)
                    ·
                      rfl

theorem cell23_8043115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 8].length) (baseStart_8043115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043115 prefixEnd_8043115 := by exact prefixLift 8043115
  have htrace : WordTrace (prefixWord ++ tailWord_8043115) baseStart_8043115 baseEnd_8043115 := by
    simpa [prefixWord, tailWord_8043115, baseEnd_8043115] using wordTrace_append hprefix tailTrace_8043115
  have hstable : (prefixWord ++ tailWord_8043115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043115).length < 2 ^ (prefixWord ++ tailWord_8043115).sum := by decide
  have hdescent : baseEnd_8043115 < baseStart_8043115 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043139 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 1, 4, 2]
def baseStart_8043139 : Nat := 118140960795 + 8043139 * 2 ^ 59
def prefixEnd_8043139 : Nat := 4983230072969 + 3 ^ 40 * 8043139 * 2
def baseEnd_8043139 : Nat := 4129996277923111915372783

theorem tailTrace_8043139 : CollatzResearch.WordTrace tailWord_8043139 prefixEnd_8043139 4129996277923111915372783 := by
  unfold tailWord_8043139
  simp only [CollatzResearch.WordTrace]
  refine ⟨293357379608088536623748471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195571586405392357749165647 293357379608088536623748471)
  ·
    refine ⟨440036069412132804935622707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293357379608088536623748471 440036069412132804935622707)
    ·
      refine ⟨660054104118199207403434061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440036069412132804935622707 660054104118199207403434061)
      ·
        refine ⟨247520289044324702776287773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 660054104118199207403434061 247520289044324702776287773)
        ·
          refine ⟨92820108391621763541107915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247520289044324702776287773 92820108391621763541107915)
          ·
            refine ⟨139230162587432645311661873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92820108391621763541107915 139230162587432645311661873)
            ·
              refine ⟨104422621940574483983746405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139230162587432645311661873 104422621940574483983746405)
              ·
                refine ⟨19579241613857715746952451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104422621940574483983746405 19579241613857715746952451)
                ·
                  refine ⟨29368862420786573620428677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19579241613857715746952451 29368862420786573620428677)
                  ·
                    refine ⟨5506661703897482553830377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29368862420786573620428677 5506661703897482553830377)
                    ·
                      refine ⟨4129996277923111915372783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506661703897482553830377 4129996277923111915372783)
                      ·
                        rfl

theorem cell23_8043139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 4, 2].length) (baseStart_8043139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043139 prefixEnd_8043139 := by exact prefixLift 8043139
  have htrace : WordTrace (prefixWord ++ tailWord_8043139) baseStart_8043139 baseEnd_8043139 := by
    simpa [prefixWord, tailWord_8043139, baseEnd_8043139] using wordTrace_append hprefix tailTrace_8043139
  have hstable : (prefixWord ++ tailWord_8043139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043139).length < 2 ^ (prefixWord ++ tailWord_8043139).sum := by decide
  have hdescent : baseEnd_8043139 < baseStart_8043139 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043190 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2]
def baseStart_8043190 : Nat := 118140960795 + 8043190 * 2 ^ 59
def prefixEnd_8043190 : Nat := 4983230072969 + 3 ^ 40 * 8043190 * 2
def baseEnd_8043190 : Nat := 4130022465436491215835049

theorem tailTrace_8043190 : CollatzResearch.WordTrace tailWord_8043190 prefixEnd_8043190 4130022465436491215835049 := by
  unfold tailWord_8043190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18334952483181485770865939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195572826487269181555903349 18334952483181485770865939)
  ·
    refine ⟨27502428724772228656298909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18334952483181485770865939 27502428724772228656298909)
    ·
      refine ⟨10313410771789585746112091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27502428724772228656298909 10313410771789585746112091)
      ·
        refine ⟨15470116157684378619168137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10313410771789585746112091 15470116157684378619168137)
        ·
          refine ⟨11602587118263283964376103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15470116157684378619168137 11602587118263283964376103)
          ·
            refine ⟨17403880677394925946564155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11602587118263283964376103 17403880677394925946564155)
            ·
              refine ⟨26105821016092388919846233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17403880677394925946564155 26105821016092388919846233)
              ·
                refine ⟨19579365762069291689884675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26105821016092388919846233 19579365762069291689884675)
                ·
                  refine ⟨29369048643103937534827013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19579365762069291689884675 29369048643103937534827013)
                  ·
                    refine ⟨5506696620581988287780065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29369048643103937534827013 5506696620581988287780065)
                    ·
                      refine ⟨4130022465436491215835049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506696620581988287780065 4130022465436491215835049)
                      ·
                        rfl

theorem cell23_8043190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_8043190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043190 prefixEnd_8043190 := by exact prefixLift 8043190
  have htrace : WordTrace (prefixWord ++ tailWord_8043190) baseStart_8043190 baseEnd_8043190 := by
    simpa [prefixWord, tailWord_8043190, baseEnd_8043190] using wordTrace_append hprefix tailTrace_8043190
  have hstable : (prefixWord ++ tailWord_8043190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043190).length < 2 ^ (prefixWord ++ tailWord_8043190).sum := by decide
  have hdescent : baseEnd_8043190 < baseStart_8043190 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043246 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4]
def baseStart_8043246 : Nat := 118140960795 + 8043246 * 2 ^ 59
def prefixEnd_8043246 : Nat := 4983230072969 + 3 ^ 40 * 8043246 * 2
def baseEnd_8043246 : Nat := 4130051220353142996734791

theorem tailTrace_8043246 : CollatzResearch.WordTrace tailWord_8043246 prefixEnd_8043246 4130051220353142996734791 := by
  unfold tailWord_8043246
  simp only [CollatzResearch.WordTrace]
  refine ⟨36670160277337611737236699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195574188145800595931929061 36670160277337611737236699)
  ·
    refine ⟨55005240416006417605855049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36670160277337611737236699 55005240416006417605855049)
    ·
      refine ⟨41253930312004813204391287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55005240416006417605855049 41253930312004813204391287)
      ·
        refine ⟨61880895468007219806586931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41253930312004813204391287 61880895468007219806586931)
        ·
          refine ⟨92821343202010829709880397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61880895468007219806586931 92821343202010829709880397)
          ·
            refine ⟨34808003700754061141205149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92821343202010829709880397 34808003700754061141205149)
            ·
              refine ⟨13053001387782772927951931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34808003700754061141205149 13053001387782772927951931)
              ·
                refine ⟨19579502081674159391927897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13053001387782772927951931 19579502081674159391927897)
                ·
                  refine ⟨14684626561255619543945923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19579502081674159391927897 14684626561255619543945923)
                  ·
                    refine ⟨22026939841883429315918885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14684626561255619543945923 22026939841883429315918885)
                    ·
                      refine ⟨4130051220353142996734791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22026939841883429315918885 4130051220353142996734791)
                      ·
                        rfl

theorem cell23_8043246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_8043246 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043246 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043246 prefixEnd_8043246 := by exact prefixLift 8043246
  have htrace : WordTrace (prefixWord ++ tailWord_8043246) baseStart_8043246 baseEnd_8043246 := by
    simpa [prefixWord, tailWord_8043246, baseEnd_8043246] using wordTrace_append hprefix tailTrace_8043246
  have hstable : (prefixWord ++ tailWord_8043246).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043246).length < 2 ^ (prefixWord ++ tailWord_8043246).sum := by decide
  have hdescent : baseEnd_8043246 < baseStart_8043246 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043249 : List Nat := [1, 2, 2, 2, 2, 2, 3, 1, 1, 4, 3]
def baseStart_8043249 : Nat := 118140960795 + 8043249 * 2 ^ 59
def prefixEnd_8043249 : Nat := 4983230072969 + 3 ^ 40 * 8043249 * 2
def baseEnd_8043249 : Nat := 4130052760795106484997277

theorem tailTrace_8043249 : CollatzResearch.WordTrace tailWord_8043249 prefixEnd_8043249 4130052760795106484997277 := by
  unfold tailWord_8043249
  simp only [CollatzResearch.WordTrace]
  refine ⟨293361391637690025410252801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195574261091793350273501867 293361391637690025410252801)
  ·
    refine ⟨220021043728267519057689601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293361391637690025410252801 220021043728267519057689601)
    ·
      refine ⟨165015782796200639293267201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220021043728267519057689601 165015782796200639293267201)
      ·
        refine ⟨123761837097150479469950401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165015782796200639293267201 123761837097150479469950401)
        ·
          refine ⟨92821377822862859602462801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123761837097150479469950401 92821377822862859602462801)
          ·
            refine ⟨69616033367147144701847101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92821377822862859602462801 69616033367147144701847101)
            ·
              refine ⟨26106012512680179263192663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69616033367147144701847101 26106012512680179263192663)
              ·
                refine ⟨39159018769020268894788995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26106012512680179263192663 39159018769020268894788995)
                ·
                  refine ⟨58738528153530403342183493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39159018769020268894788995 58738528153530403342183493)
                  ·
                    refine ⟨11013474028786950626659405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58738528153530403342183493 11013474028786950626659405)
                    ·
                      refine ⟨4130052760795106484997277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11013474028786950626659405 4130052760795106484997277)
                      ·
                        rfl

theorem cell23_8043249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_8043249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043249 prefixEnd_8043249 := by exact prefixLift 8043249
  have htrace : WordTrace (prefixWord ++ tailWord_8043249) baseStart_8043249 baseEnd_8043249 := by
    simpa [prefixWord, tailWord_8043249, baseEnd_8043249] using wordTrace_append hprefix tailTrace_8043249
  have hstable : (prefixWord ++ tailWord_8043249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043249).length < 2 ^ (prefixWord ++ tailWord_8043249).sum := by decide
  have hdescent : baseEnd_8043249 < baseStart_8043249 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043349 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 6]
def baseStart_8043349 : Nat := 118140960795 + 8043349 * 2 ^ 59
def prefixEnd_8043349 : Nat := 4983230072969 + 3 ^ 40 * 8043349 * 2
def baseEnd_8043349 : Nat := 4130104108860556093746817

theorem tailTrace_8043349 : CollatzResearch.WordTrace tailWord_8043349 prefixEnd_8043349 4130104108860556093746817 := by
  unfold tailWord_8043349
  simp only [CollatzResearch.WordTrace]
  refine ⟨293365038937327742488893101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195576692624885161659262067 293365038937327742488893101)
  ·
    refine ⟨110011889601497903433334913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293365038937327742488893101 110011889601497903433334913)
    ·
      refine ⟨82508917201123427575001185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110011889601497903433334913 82508917201123427575001185)
      ·
        refine ⟨61881687900842570681250889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82508917201123427575001185 61881687900842570681250889)
        ·
          refine ⟨46411265925631928010938167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61881687900842570681250889 46411265925631928010938167)
          ·
            refine ⟨69616898888447892016407251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46411265925631928010938167 69616898888447892016407251)
            ·
              refine ⟨104425348332671838024610877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69616898888447892016407251 104425348332671838024610877)
              ·
                refine ⟨39159505624751939259229079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104425348332671838024610877 39159505624751939259229079)
                ·
                  refine ⟨58739258437127908888843619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39159505624751939259229079 58739258437127908888843619)
                  ·
                    refine ⟨88108887655691863333265429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58739258437127908888843619 88108887655691863333265429)
                    ·
                      refine ⟨4130104108860556093746817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88108887655691863333265429 4130104108860556093746817)
                      ·
                        rfl

theorem cell23_8043349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_8043349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043349 prefixEnd_8043349 := by exact prefixLift 8043349
  have htrace : WordTrace (prefixWord ++ tailWord_8043349) baseStart_8043349 baseEnd_8043349 := by
    simpa [prefixWord, tailWord_8043349, baseEnd_8043349] using wordTrace_append hprefix tailTrace_8043349
  have hstable : (prefixWord ++ tailWord_8043349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043349).length < 2 ^ (prefixWord ++ tailWord_8043349).sum := by decide
  have hdescent : baseEnd_8043349 < baseStart_8043349 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043353 : List Nat := [1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 4]
def baseStart_8043353 : Nat := 118140960795 + 8043353 * 2 ^ 59
def prefixEnd_8043353 : Nat := 4983230072969 + 3 ^ 40 * 8043353 * 2
def baseEnd_8043353 : Nat := 4130106162783174078096799

theorem tailTrace_8043353 : CollatzResearch.WordTrace tailWord_8043353 prefixEnd_8043353 4130106162783174078096799 := by
  unfold tailWord_8043353
  simp only [CollatzResearch.WordTrace]
  refine ⟨293365184829313251172038713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195576789886208834114692475 293365184829313251172038713)
  ·
    refine ⟨220023888621984938379029035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293365184829313251172038713 220023888621984938379029035)
    ·
      refine ⟨330035832932977407568543553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220023888621984938379029035 330035832932977407568543553)
      ·
        refine ⟨247526874699733055676407665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330035832932977407568543553 247526874699733055676407665)
        ·
          refine ⟨185645156024799791757305749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247526874699733055676407665 185645156024799791757305749)
          ·
            refine ⟨8702116688662490238623707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185645156024799791757305749 8702116688662490238623707)
            ·
              refine ⟨13053175032993735357935561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8702116688662490238623707 13053175032993735357935561)
              ·
                refine ⟨9789881274745301518451671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13053175032993735357935561 9789881274745301518451671)
                ·
                  refine ⟨14684821912117952277677507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9789881274745301518451671 14684821912117952277677507)
                  ·
                    refine ⟨22027232868176928416516261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14684821912117952277677507 22027232868176928416516261)
                    ·
                      refine ⟨4130106162783174078096799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22027232868176928416516261 4130106162783174078096799)
                      ·
                        rfl

theorem cell23_8043353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 1, 2, 1, 1, 4].length) (baseStart_8043353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043353 prefixEnd_8043353 := by exact prefixLift 8043353
  have htrace : WordTrace (prefixWord ++ tailWord_8043353) baseStart_8043353 baseEnd_8043353 := by
    simpa [prefixWord, tailWord_8043353, baseEnd_8043353] using wordTrace_append hprefix tailTrace_8043353
  have hstable : (prefixWord ++ tailWord_8043353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043353).length < 2 ^ (prefixWord ++ tailWord_8043353).sum := by decide
  have hdescent : baseEnd_8043353 < baseStart_8043353 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043387 : List Nat := [1, 1, 1, 1, 1, 5, 6, 2, 1, 2, 2]
def baseStart_8043387 : Nat := 118140960795 + 8043387 * 2 ^ 59
def prefixEnd_8043387 : Nat := 4983230072969 + 3 ^ 40 * 8043387 * 2
def baseEnd_8043387 : Nat := 4130123621125426945071643

theorem tailTrace_8043387 : CollatzResearch.WordTrace tailWord_8043387 prefixEnd_8043387 4130123621125426945071643 := by
  unfold tailWord_8043387
  simp only [CollatzResearch.WordTrace]
  refine ⟨293366424911190074978776415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195577616607460049985850943 293366424911190074978776415)
  ·
    refine ⟨440049637366785112468164623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293366424911190074978776415 440049637366785112468164623)
    ·
      refine ⟨660074456050177668702246935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440049637366785112468164623 660074456050177668702246935)
      ·
        refine ⟨990111684075266503053370403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660074456050177668702246935 990111684075266503053370403)
        ·
          refine ⟨1485167526112899754580055605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990111684075266503053370403 1485167526112899754580055605)
          ·
            refine ⟨139234455573084351991880213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1485167526112899754580055605 139234455573084351991880213)
            ·
              refine ⟨6526615104988328999619385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139234455573084351991880213 6526615104988328999619385)
              ·
                refine ⟨4894961328741246749714539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6526615104988328999619385 4894961328741246749714539)
                ·
                  refine ⟨7342441993111870124571809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4894961328741246749714539 7342441993111870124571809)
                  ·
                    refine ⟨5506831494833902593428857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7342441993111870124571809 5506831494833902593428857)
                    ·
                      refine ⟨4130123621125426945071643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506831494833902593428857 4130123621125426945071643)
                      ·
                        rfl

theorem cell23_8043387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 6, 2, 1, 2, 2].length) (baseStart_8043387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043387 prefixEnd_8043387 := by exact prefixLift 8043387
  have htrace : WordTrace (prefixWord ++ tailWord_8043387) baseStart_8043387 baseEnd_8043387 := by
    simpa [prefixWord, tailWord_8043387, baseEnd_8043387] using wordTrace_append hprefix tailTrace_8043387
  have hstable : (prefixWord ++ tailWord_8043387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043387).length < 2 ^ (prefixWord ++ tailWord_8043387).sum := by decide
  have hdescent : baseEnd_8043387 < baseStart_8043387 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043389 : List Nat := [1, 4, 1, 1, 2, 1, 3, 1, 2, 7]
def baseStart_8043389 : Nat := 118140960795 + 8043389 * 2 ^ 59
def prefixEnd_8043389 : Nat := 4983230072969 + 3 ^ 40 * 8043389 * 2
def baseEnd_8043389 : Nat := 1376708216028911979082211

theorem tailTrace_8043389 : CollatzResearch.WordTrace tailWord_8043389 prefixEnd_8043389 1376708216028911979082211 := by
  unfold tailWord_8043389
  simp only [CollatzResearch.WordTrace]
  refine ⟨293366497857182829320349221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195577665238121886213566147 293366497857182829320349221)
  ·
    refine ⟨55006218348221780497565479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293366497857182829320349221 55006218348221780497565479)
    ·
      refine ⟨82509327522332670746348219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55006218348221780497565479 82509327522332670746348219)
      ·
        refine ⟨123763991283499006119522329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82509327522332670746348219 123763991283499006119522329)
        ·
          refine ⟨92822993462624254589641747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123763991283499006119522329 92822993462624254589641747)
          ·
            refine ⟨139234490193936381884462621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92822993462624254589641747 139234490193936381884462621)
            ·
              refine ⟨52212933822726143206673483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139234490193936381884462621 52212933822726143206673483)
              ·
                refine ⟨78319400734089214810010225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52212933822726143206673483 78319400734089214810010225)
                ·
                  refine ⟨58739550550566911107507669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78319400734089214810010225 58739550550566911107507669)
                  ·
                    refine ⟨1376708216028911979082211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58739550550566911107507669 1376708216028911979082211)
                    ·
                      rfl

theorem cell23_8043389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_8043389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043389 prefixEnd_8043389 := by exact prefixLift 8043389
  have htrace : WordTrace (prefixWord ++ tailWord_8043389) baseStart_8043389 baseEnd_8043389 := by
    simpa [prefixWord, tailWord_8043389, baseEnd_8043389] using wordTrace_append hprefix tailTrace_8043389
  have hstable : (prefixWord ++ tailWord_8043389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043389).length < 2 ^ (prefixWord ++ tailWord_8043389).sum := by decide
  have hdescent : baseEnd_8043389 < baseStart_8043389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043403 : List Nat := [1, 1, 1, 1, 4, 2, 4, 3, 2, 1, 3]
def baseStart_8043403 : Nat := 118140960795 + 8043403 * 2 ^ 59
def prefixEnd_8043403 : Nat := 4983230072969 + 3 ^ 40 * 8043403 * 2
def baseEnd_8043403 : Nat := 4130131836815898882471569

theorem tailTrace_8043403 : CollatzResearch.WordTrace tailWord_8043403 prefixEnd_8043403 4130131836815898882471569 := by
  unfold tailWord_8043403
  simp only [CollatzResearch.WordTrace]
  refine ⟨293367008479132109711358863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195578005652754739807572575 293367008479132109711358863)
  ·
    refine ⟨440050512718698164567038295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293367008479132109711358863 440050512718698164567038295)
    ·
      refine ⟨660075769078047246850557443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440050512718698164567038295 660075769078047246850557443)
      ·
        refine ⟨990113653617070870275836165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660075769078047246850557443 990113653617070870275836165)
        ·
          refine ⟨185646310053200788176719281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 990113653617070870275836165 185646310053200788176719281)
          ·
            refine ⟨139234732539900591132539461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185646310053200788176719281 139234732539900591132539461)
            ·
              refine ⟨26106512351231360837351149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139234732539900591132539461 26106512351231360837351149)
              ·
                refine ⟨9789942131711760314006681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26106512351231360837351149 9789942131711760314006681)
                ·
                  refine ⟨7342456598783820235505011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9789942131711760314006681 7342456598783820235505011)
                  ·
                    refine ⟨11013684898175730353257517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7342456598783820235505011 11013684898175730353257517)
                    ·
                      refine ⟨4130131836815898882471569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11013684898175730353257517 4130131836815898882471569)
                      ·
                        rfl

theorem cell23_8043403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 1, 3].length) (baseStart_8043403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043403 prefixEnd_8043403 := by exact prefixLift 8043403
  have htrace : WordTrace (prefixWord ++ tailWord_8043403) baseStart_8043403 baseEnd_8043403 := by
    simpa [prefixWord, tailWord_8043403, baseEnd_8043403] using wordTrace_append hprefix tailTrace_8043403
  have hstable : (prefixWord ++ tailWord_8043403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043403).length < 2 ^ (prefixWord ++ tailWord_8043403).sum := by decide
  have hdescent : baseEnd_8043403 < baseStart_8043403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043409 : List Nat := [1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 4]
def baseStart_8043409 : Nat := 118140960795 + 8043409 * 2 ^ 59
def prefixEnd_8043409 : Nat := 4983230072969 + 3 ^ 40 * 8043409 * 2
def baseEnd_8043409 : Nat := 4130134917699825858996541

theorem tailTrace_8043409 : CollatzResearch.WordTrace tailWord_8043409 prefixEnd_8043409 4130134917699825858996541 := by
  unfold tailWord_8043409
  simp only [CollatzResearch.WordTrace]
  refine ⟨293367227317110372736077281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195578151544740248490718187 293367227317110372736077281)
  ·
    refine ⟨220025420487832779552057961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293367227317110372736077281 220025420487832779552057961)
    ·
      refine ⟨165019065365874584664043471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220025420487832779552057961 165019065365874584664043471)
      ·
        refine ⟨247528598048811876996065207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165019065365874584664043471 247528598048811876996065207)
        ·
          refine ⟨371292897073217815494097811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247528598048811876996065207 371292897073217815494097811)
          ·
            refine ⟨556939345609826723241146717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371292897073217815494097811 556939345609826723241146717)
            ·
              refine ⟨208852254603685021215430019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556939345609826723241146717 208852254603685021215430019)
              ·
                refine ⟨313278381905527531823145029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208852254603685021215430019 313278381905527531823145029)
                ·
                  refine ⟨58739696607286412216839693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 313278381905527531823145029 58739696607286412216839693)
                  ·
                    refine ⟨22027386227732404581314885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58739696607286412216839693 22027386227732404581314885)
                    ·
                      refine ⟨4130134917699825858996541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22027386227732404581314885 4130134917699825858996541)
                      ·
                        rfl

theorem cell23_8043409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 4].length) (baseStart_8043409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043409 prefixEnd_8043409 := by exact prefixLift 8043409
  have htrace : WordTrace (prefixWord ++ tailWord_8043409) baseStart_8043409 baseEnd_8043409 := by
    simpa [prefixWord, tailWord_8043409, baseEnd_8043409] using wordTrace_append hprefix tailTrace_8043409
  have hstable : (prefixWord ++ tailWord_8043409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043409).length < 2 ^ (prefixWord ++ tailWord_8043409).sum := by decide
  have hdescent : baseEnd_8043409 < baseStart_8043409 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043413 : List Nat := [1, 3, 2, 1, 1, 4, 2, 1, 3, 3, 2]
def baseStart_8043413 : Nat := 118140960795 + 8043413 * 2 ^ 59
def prefixEnd_8043413 : Nat := 4983230072969 + 3 ^ 40 * 8043413 * 2
def baseEnd_8043413 : Nat := 4130136971622443843346523

theorem tailTrace_8043413 : CollatzResearch.WordTrace tailWord_8043413 prefixEnd_8043413 4130136971622443843346523 := by
  unfold tailWord_8043413
  simp only [CollatzResearch.WordTrace]
  refine ⟨293367373209095881419222893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195578248806063920946148595 293367373209095881419222893)
  ·
    refine ⟨110012764953410955532208585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293367373209095881419222893 110012764953410955532208585)
    ·
      refine ⟨82509573715058216649156439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110012764953410955532208585 82509573715058216649156439)
      ·
        refine ⟨123764360572587324973734659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82509573715058216649156439 123764360572587324973734659)
        ·
          refine ⟨185646540858880987460601989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123764360572587324973734659 185646540858880987460601989)
          ·
            refine ⟨34808726411040185148862873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185646540858880987460601989 34808726411040185148862873)
            ·
              refine ⟨26106544808280138861647155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34808726411040185148862873 26106544808280138861647155)
              ·
                refine ⟨39159817212420208292470733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26106544808280138861647155 39159817212420208292470733)
                ·
                  refine ⟨14684931454657578109676525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39159817212420208292470733 14684931454657578109676525)
                  ·
                    refine ⟨5506849295496591791128697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14684931454657578109676525 5506849295496591791128697)
                    ·
                      refine ⟨4130136971622443843346523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5506849295496591791128697 4130136971622443843346523)
                      ·
                        rfl

theorem cell23_8043413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_8043413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043413 prefixEnd_8043413 := by exact prefixLift 8043413
  have htrace : WordTrace (prefixWord ++ tailWord_8043413) baseStart_8043413 baseEnd_8043413 := by
    simpa [prefixWord, tailWord_8043413, baseEnd_8043413] using wordTrace_append hprefix tailTrace_8043413
  have hstable : (prefixWord ++ tailWord_8043413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043413).length < 2 ^ (prefixWord ++ tailWord_8043413).sum := by decide
  have hdescent : baseEnd_8043413 < baseStart_8043413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043437 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 4, 1, 3]
def baseStart_8043437 : Nat := 118140960795 + 8043437 * 2 ^ 59
def prefixEnd_8043437 : Nat := 4983230072969 + 3 ^ 40 * 8043437 * 2
def baseEnd_8043437 : Nat := 4130149295158151749446413

theorem tailTrace_8043437 : CollatzResearch.WordTrace tailWord_8043437 prefixEnd_8043437 4130149295158151749446413 := by
  unfold tailWord_8043437
  simp only [CollatzResearch.WordTrace]
  refine ⟨293368248561008933518096565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195578832374005955678731043 293368248561008933518096565)
  ·
    refine ⟨27503273302594587517321553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293368248561008933518096565 27503273302594587517321553)
    ·
      refine ⟨20627454976945940637991165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27503273302594587517321553 20627454976945940637991165)
      ·
        refine ⟨7735295616354727739246687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20627454976945940637991165 7735295616354727739246687)
        ·
          refine ⟨11602943424532091608870031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7735295616354727739246687 11602943424532091608870031)
          ·
            refine ⟨17404415136798137413305047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11602943424532091608870031 17404415136798137413305047)
            ·
              refine ⟨26106622705197206119957571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17404415136798137413305047 26106622705197206119957571)
              ·
                refine ⟨39159934057795809179936357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26106622705197206119957571 39159934057795809179936357)
                ·
                  refine ⟨7342487635836714221238067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39159934057795809179936357 7342487635836714221238067)
                  ·
                    refine ⟨11013731453755071331857101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7342487635836714221238067 11013731453755071331857101)
                    ·
                      refine ⟨4130149295158151749446413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11013731453755071331857101 4130149295158151749446413)
                      ·
                        rfl

theorem cell23_8043437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_8043437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043437 prefixEnd_8043437 := by exact prefixLift 8043437
  have htrace : WordTrace (prefixWord ++ tailWord_8043437) baseStart_8043437 baseEnd_8043437 := by
    simpa [prefixWord, tailWord_8043437, baseEnd_8043437] using wordTrace_append hprefix tailTrace_8043437
  have hstable : (prefixWord ++ tailWord_8043437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043437).length < 2 ^ (prefixWord ++ tailWord_8043437).sum := by decide
  have hdescent : baseEnd_8043437 < baseStart_8043437 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043456 : List Nat := [2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 4]
def baseStart_8043456 : Nat := 118140960795 + 8043456 * 2 ^ 59
def prefixEnd_8043456 : Nat := 4983230072969 + 3 ^ 40 * 8043456 * 2
def baseEnd_8043456 : Nat := 4130159051290587175108825

theorem tailTrace_8043456 : CollatzResearch.WordTrace tailWord_8043456 prefixEnd_8043456 4130159051290587175108825 := by
  unfold tailWord_8043456
  simp only [CollatzResearch.WordTrace]
  refine ⟨146684470773970049881519111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195579294365293399842025481 146684470773970049881519111)
  ·
    refine ⟨220026706160955074822278667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146684470773970049881519111 220026706160955074822278667)
    ·
      refine ⟨330040059241432612233418001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220026706160955074822278667 330040059241432612233418001)
      ·
        refine ⟨247530044431074459175063501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330040059241432612233418001 247530044431074459175063501)
        ·
          refine ⟨92823766661652922190648813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247530044431074459175063501 92823766661652922190648813)
          ·
            refine ⟨34808912498119845821493305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92823766661652922190648813 34808912498119845821493305)
            ·
              refine ⟨26106684373589884366119979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34808912498119845821493305 26106684373589884366119979)
              ·
                refine ⟨39160026560384826549179969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26106684373589884366119979 39160026560384826549179969)
                ·
                  refine ⟨29370019920288619911884977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39160026560384826549179969 29370019920288619911884977)
                  ·
                    refine ⟨22027514940216464933913733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29370019920288619911884977 22027514940216464933913733)
                    ·
                      refine ⟨4130159051290587175108825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22027514940216464933913733 4130159051290587175108825)
                      ·
                        rfl

theorem cell23_8043456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_8043456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043456 prefixEnd_8043456 := by exact prefixLift 8043456
  have htrace : WordTrace (prefixWord ++ tailWord_8043456) baseStart_8043456 baseEnd_8043456 := by
    simpa [prefixWord, tailWord_8043456, baseEnd_8043456] using wordTrace_append hprefix tailTrace_8043456
  have hstable : (prefixWord ++ tailWord_8043456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043456).length < 2 ^ (prefixWord ++ tailWord_8043456).sum := by decide
  have hdescent : baseEnd_8043456 < baseStart_8043456 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043496 : List Nat := [2, 1, 4, 1, 1, 1, 3, 1, 4, 5]
def baseStart_8043496 : Nat := 118140960795 + 8043496 * 2 ^ 59
def prefixEnd_8043496 : Nat := 4983230072969 + 3 ^ 40 * 8043496 * 2
def baseEnd_8043496 : Nat := 1376726530172255672869547

theorem tailTrace_8043496 : CollatzResearch.WordTrace tailWord_8043496 prefixEnd_8043496 1376726530172255672869547 := by
  unfold tailWord_8043496
  simp only [CollatzResearch.WordTrace]
  refine ⟨146685200233897593297247171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195580266978530124396329561 146685200233897593297247171)
  ·
    refine ⟨220027800350846389945870757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146685200233897593297247171 220027800350846389945870757)
    ·
      refine ⟨41255212565783698114850767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220027800350846389945870757 41255212565783698114850767)
      ·
        refine ⟨61882818848675547172276151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41255212565783698114850767 61882818848675547172276151)
        ·
          refine ⟨92824228273013320758414227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61882818848675547172276151 92824228273013320758414227)
          ·
            refine ⟨139236342409519981137621341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92824228273013320758414227 139236342409519981137621341)
            ·
              refine ⟨52213628403569992926608003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139236342409519981137621341 52213628403569992926608003)
              ·
                refine ⟨78320442605354989389912005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52213628403569992926608003 78320442605354989389912005)
                ·
                  refine ⟨14685082988504060510608501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78320442605354989389912005 14685082988504060510608501)
                  ·
                    refine ⟨1376726530172255672869547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14685082988504060510608501 1376726530172255672869547)
                    ·
                      rfl

theorem cell23_8043496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_8043496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043496 prefixEnd_8043496 := by exact prefixLift 8043496
  have htrace : WordTrace (prefixWord ++ tailWord_8043496) baseStart_8043496 baseEnd_8043496 := by
    simpa [prefixWord, tailWord_8043496, baseEnd_8043496] using wordTrace_append hprefix tailTrace_8043496
  have hstable : (prefixWord ++ tailWord_8043496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043496).length < 2 ^ (prefixWord ++ tailWord_8043496).sum := by decide
  have hdescent : baseEnd_8043496 < baseStart_8043496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043499 : List Nat := [1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 8]
def baseStart_8043499 : Nat := 118140960795 + 8043499 * 2 ^ 59
def prefixEnd_8043499 : Nat := 4983230072969 + 3 ^ 40 * 8043499 * 2
def baseEnd_8043499 : Nat := 4130181130958730506871127

theorem tailTrace_8043499 : CollatzResearch.WordTrace tailWord_8043499 prefixEnd_8043499 4130181130958730506871127 := by
  unfold tailWord_8043499
  simp only [CollatzResearch.WordTrace]
  refine ⟨293370509886784318106853551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195580339924522878737902367 293370509886784318106853551)
  ·
    refine ⟨440055764830176477160280327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293370509886784318106853551 440055764830176477160280327)
    ·
      refine ⟨660083647245264715740420491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440055764830176477160280327 660083647245264715740420491)
      ·
        refine ⟨990125470867897073610630737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660083647245264715740420491 990125470867897073610630737)
        ·
          refine ⟨742594103150922805207973053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990125470867897073610630737 742594103150922805207973053)
          ·
            refine ⟨278472788681596051952989895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 742594103150922805207973053 278472788681596051952989895)
            ·
              refine ⟨417709183022394077929484843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278472788681596051952989895 417709183022394077929484843)
              ·
                refine ⟨626563774533591116894227265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417709183022394077929484843 626563774533591116894227265)
                ·
                  refine ⟨469922830900193337670670449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 626563774533591116894227265 469922830900193337670670449)
                  ·
                    refine ⟨352442123175145003253002837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 469922830900193337670670449 352442123175145003253002837)
                    ·
                      refine ⟨4130181130958730506871127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 352442123175145003253002837 4130181130958730506871127)
                      ·
                        rfl

theorem cell23_8043499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 8].length) (baseStart_8043499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043499 prefixEnd_8043499 := by exact prefixLift 8043499
  have htrace : WordTrace (prefixWord ++ tailWord_8043499) baseStart_8043499 baseEnd_8043499 := by
    simpa [prefixWord, tailWord_8043499, baseEnd_8043499] using wordTrace_append hprefix tailTrace_8043499
  have hstable : (prefixWord ++ tailWord_8043499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043499).length < 2 ^ (prefixWord ++ tailWord_8043499).sum := by decide
  have hdescent : baseEnd_8043499 < baseStart_8043499 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043546 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6]
def baseStart_8043546 : Nat := 118140960795 + 8043546 * 2 ^ 59
def prefixEnd_8043546 : Nat := 4983230072969 + 3 ^ 40 * 8043546 * 2
def baseEnd_8043546 : Nat := 4130205264549491822983411

theorem tailTrace_8043546 : CollatzResearch.WordTrace tailWord_8043546 prefixEnd_8043546 4130205264549491822983411 := by
  unfold tailWord_8043546
  simp only [CollatzResearch.WordTrace]
  refine ⟨73343056029403511283453623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195581482745076030089209661 73343056029403511283453623)
  ·
    refine ⟨110014584044105266925180435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73343056029403511283453623 110014584044105266925180435)
    ·
      refine ⟨165021876066157900387770653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110014584044105266925180435 165021876066157900387770653)
      ·
        refine ⟨61883203524809212645413995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165021876066157900387770653 61883203524809212645413995)
        ·
          refine ⟨92824805287213818968120993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61883203524809212645413995 92824805287213818968120993)
          ·
            refine ⟨69618603965410364226090745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92824805287213818968120993 69618603965410364226090745)
            ·
              refine ⟨52213952974057773169568059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69618603965410364226090745 52213952974057773169568059)
              ·
                refine ⟨78320929461086659754352089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52213952974057773169568059 78320929461086659754352089)
                ·
                  refine ⟨58740697095814994815764067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78320929461086659754352089 58740697095814994815764067)
                  ·
                    refine ⟨88111045643722492223646101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58740697095814994815764067 88111045643722492223646101)
                    ·
                      refine ⟨4130205264549491822983411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88111045643722492223646101 4130205264549491822983411)
                      ·
                        rfl

theorem cell23_8043546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_8043546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043546 prefixEnd_8043546 := by exact prefixLift 8043546
  have htrace : WordTrace (prefixWord ++ tailWord_8043546) baseStart_8043546 baseEnd_8043546 := by
    simpa [prefixWord, tailWord_8043546, baseEnd_8043546] using wordTrace_append hprefix tailTrace_8043546
  have hstable : (prefixWord ++ tailWord_8043546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043546).length < 2 ^ (prefixWord ++ tailWord_8043546).sum := by decide
  have hdescent : baseEnd_8043546 < baseStart_8043546 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043596 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 2, 4, 5]
def baseStart_8043596 : Nat := 118140960795 + 8043596 * 2 ^ 59
def prefixEnd_8043596 : Nat := 4983230072969 + 3 ^ 40 * 8043596 * 2
def baseEnd_8043596 : Nat := 4130230938582216627358181

theorem tailTrace_8043596 : CollatzResearch.WordTrace tailWord_8043596 prefixEnd_8043596 4130230938582216627358181 := by
  unfold tailWord_8043596
  simp only [CollatzResearch.WordTrace]
  refine ⟨146687023883716451836567321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195582698511621935782089761 146687023883716451836567321)
  ·
    refine ⟨110015267912787338877425491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146687023883716451836567321 110015267912787338877425491)
    ·
      refine ⟨165022901869181008316138237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110015267912787338877425491 165022901869181008316138237)
      ·
        refine ⟨61883588200942878118551839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165022901869181008316138237 61883588200942878118551839)
        ·
          refine ⟨92825382301414317177827759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61883588200942878118551839 92825382301414317177827759)
          ·
            refine ⟨139238073452121475766741639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92825382301414317177827759 139238073452121475766741639)
            ·
              refine ⟨208857110178182213650112459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139238073452121475766741639 208857110178182213650112459)
              ·
                refine ⟨313285665267273320475168689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208857110178182213650112459 313285665267273320475168689)
                ·
                  refine ⟨234964248950454990356376517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313285665267273320475168689 234964248950454990356376517)
                  ·
                    refine ⟨44055796678210310691820597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 234964248950454990356376517 44055796678210310691820597)
                    ·
                      refine ⟨4130230938582216627358181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44055796678210310691820597 4130230938582216627358181)
                      ·
                        rfl

theorem cell23_8043596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_8043596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043596 prefixEnd_8043596 := by exact prefixLift 8043596
  have htrace : WordTrace (prefixWord ++ tailWord_8043596) baseStart_8043596 baseEnd_8043596 := by
    simpa [prefixWord, tailWord_8043596, baseEnd_8043596] using wordTrace_append hprefix tailTrace_8043596
  have hstable : (prefixWord ++ tailWord_8043596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043596).length < 2 ^ (prefixWord ++ tailWord_8043596).sum := by decide
  have hdescent : baseEnd_8043596 < baseStart_8043596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043617 : List Nat := [1, 2, 3, 1, 1, 2, 4, 4, 1, 1, 3]
def baseStart_8043617 : Nat := 118140960795 + 8043617 * 2 ^ 59
def prefixEnd_8043617 : Nat := 4983230072969 + 3 ^ 40 * 8043617 * 2
def baseEnd_8043617 : Nat := 4130241721675961045195585

theorem tailTrace_8043617 : CollatzResearch.WordTrace tailWord_8043617 prefixEnd_8043617 4130241721675961045195585 := by
  unfold tailWord_8043617
  simp only [CollatzResearch.WordTrace]
  refine ⟨293374813700356824259649105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195583209133571216173099403 293374813700356824259649105)
  ·
    refine ⟨220031110275267618194736829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293374813700356824259649105 220031110275267618194736829)
    ·
      refine ⟨82511666353225356823026311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220031110275267618194736829 82511666353225356823026311)
      ·
        refine ⟨123767499529838035234539467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82511666353225356823026311 123767499529838035234539467)
        ·
          refine ⟨185651249294757052851809201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123767499529838035234539467 185651249294757052851809201)
          ·
            refine ⟨139238436971067789638856901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185651249294757052851809201 139238436971067789638856901)
            ·
              refine ⟨26107206932075210557285669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139238436971067789638856901 26107206932075210557285669)
              ·
                refine ⟨4895101299764101979491063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26107206932075210557285669 4895101299764101979491063)
                ·
                  refine ⟨7342651949646152969236595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4895101299764101979491063 7342651949646152969236595)
                  ·
                    refine ⟨11013977924469229453854893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7342651949646152969236595 11013977924469229453854893)
                    ·
                      refine ⟨4130241721675961045195585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11013977924469229453854893 4130241721675961045195585)
                      ·
                        rfl

theorem cell23_8043617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 4, 4, 1, 1, 3].length) (baseStart_8043617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043617 prefixEnd_8043617 := by exact prefixLift 8043617
  have htrace : WordTrace (prefixWord ++ tailWord_8043617) baseStart_8043617 baseEnd_8043617 := by
    simpa [prefixWord, tailWord_8043617, baseEnd_8043617] using wordTrace_append hprefix tailTrace_8043617
  have hstable : (prefixWord ++ tailWord_8043617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043617).length < 2 ^ (prefixWord ++ tailWord_8043617).sum := by decide
  have hdescent : baseEnd_8043617 < baseStart_8043617 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043643 : List Nat := [1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 3]
def baseStart_8043643 : Nat := 118140960795 + 8043643 * 2 ^ 59
def prefixEnd_8043643 : Nat := 4983230072969 + 3 ^ 40 * 8043643 * 2
def baseEnd_8043643 : Nat := 4130255072172977943470465

theorem tailTrace_8043643 : CollatzResearch.WordTrace tailWord_8043643 prefixEnd_8043643 4130255072172977943470465 := by
  unfold tailWord_8043643
  simp only [CollatzResearch.WordTrace]
  refine ⟨293375761998262630700095583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195583841332175087133397055 293375761998262630700095583)
  ·
    refine ⟨440063642997393946050143375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293375761998262630700095583 440063642997393946050143375)
    ·
      refine ⟨660095464496090919075215063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440063642997393946050143375 660095464496090919075215063)
      ·
        refine ⟨990143196744136378612822595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660095464496090919075215063 990143196744136378612822595)
        ·
          refine ⟨1485214795116204567919233893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990143196744136378612822595 1485214795116204567919233893)
          ·
            refine ⟨278477774084288356484856355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1485214795116204567919233893 278477774084288356484856355)
            ·
              refine ⟨417716661126432534727284533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278477774084288356484856355 417716661126432534727284533)
              ·
                refine ⟨39160936980603050130682925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 417716661126432534727284533 39160936980603050130682925)
                ·
                  refine ⟨14685351367726143799006097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39160936980603050130682925 14685351367726143799006097)
                  ·
                    refine ⟨11014013525794607849254573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14685351367726143799006097 11014013525794607849254573)
                    ·
                      refine ⟨4130255072172977943470465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11014013525794607849254573 4130255072172977943470465)
                      ·
                        rfl

theorem cell23_8043643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 2, 3].length) (baseStart_8043643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043643 prefixEnd_8043643 := by exact prefixLift 8043643
  have htrace : WordTrace (prefixWord ++ tailWord_8043643) baseStart_8043643 baseEnd_8043643 := by
    simpa [prefixWord, tailWord_8043643, baseEnd_8043643] using wordTrace_append hprefix tailTrace_8043643
  have hstable : (prefixWord ++ tailWord_8043643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043643).length < 2 ^ (prefixWord ++ tailWord_8043643).sum := by decide
  have hdescent : baseEnd_8043643 < baseStart_8043643 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043674 : List Nat := [3, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2]
def baseStart_8043674 : Nat := 118140960795 + 8043674 * 2 ^ 59
def prefixEnd_8043674 : Nat := 4983230072969 + 3 ^ 40 * 8043674 * 2
def baseEnd_8043674 : Nat := 4130270990073267322182823

theorem tailTrace_8043674 : CollatzResearch.WordTrace tailWord_8043674 prefixEnd_8043674 4130270990073267322182823 := by
  unfold tailWord_8043674
  simp only [CollatzResearch.WordTrace]
  refine ⟨73344223165287580748618519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195584595107433548662982717 73344223165287580748618519)
  ·
    refine ⟨110016334747931371122927779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73344223165287580748618519 110016334747931371122927779)
    ·
      refine ⟨165024502121897056684391669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110016334747931371122927779 165024502121897056684391669)
      ·
        refine ⟨15471047073927849064161719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165024502121897056684391669 15471047073927849064161719)
        ·
          refine ⟨23206570610891773596242579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15471047073927849064161719 23206570610891773596242579)
          ·
            refine ⟨34809855916337660394363869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23206570610891773596242579 34809855916337660394363869)
            ·
              refine ⟨13053695968626622647886451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34809855916337660394363869 13053695968626622647886451)
              ·
                refine ⟨19580543952939933971829677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13053695968626622647886451 19580543952939933971829677)
                ·
                  refine ⟨7342703982352475239436129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19580543952939933971829677 7342703982352475239436129)
                  ·
                    refine ⟨5507027986764356429577097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7342703982352475239436129 5507027986764356429577097)
                    ·
                      refine ⟨4130270990073267322182823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5507027986764356429577097 4130270990073267322182823)
                      ·
                        rfl

theorem cell23_8043674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 1, 3, 2, 2].length) (baseStart_8043674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043674 prefixEnd_8043674 := by exact prefixLift 8043674
  have htrace : WordTrace (prefixWord ++ tailWord_8043674) baseStart_8043674 baseEnd_8043674 := by
    simpa [prefixWord, tailWord_8043674, baseEnd_8043674] using wordTrace_append hprefix tailTrace_8043674
  have hstable : (prefixWord ++ tailWord_8043674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043674).length < 2 ^ (prefixWord ++ tailWord_8043674).sum := by decide
  have hdescent : baseEnd_8043674 < baseStart_8043674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043684 : List Nat := [2, 3, 1, 2, 3, 3, 2, 1, 2, 4]
def baseStart_8043684 : Nat := 118140960795 + 8043684 * 2 ^ 59
def prefixEnd_8043684 : Nat := 4983230072969 + 3 ^ 40 * 8043684 * 2
def baseEnd_8043684 : Nat := 1376758708293270761019259

theorem tailTrace_8043684 : CollatzResearch.WordTrace tailWord_8043684 prefixEnd_8043684 1376758708293270761019259 := by
  unfold tailWord_8043684
  simp only [CollatzResearch.WordTrace]
  refine ⟨146688628695557047351169053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195584838260742729801558737 146688628695557047351169053)
  ·
    refine ⟨55008235760833892756688395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146688628695557047351169053 55008235760833892756688395)
    ·
      refine ⟨82512353641250839135032593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55008235760833892756688395 82512353641250839135032593)
      ·
        refine ⟨61884265230938129351274445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82512353641250839135032593 61884265230938129351274445)
        ·
          refine ⟨23206599461601798506727917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61884265230938129351274445 23206599461601798506727917)
          ·
            refine ⟨8702474798100674440022969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23206599461601798506727917 8702474798100674440022969)
            ·
              refine ⟨6526856098575505830017227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8702474798100674440022969 6526856098575505830017227)
              ·
                refine ⟨9790284147863258745025841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6526856098575505830017227 9790284147863258745025841)
                ·
                  refine ⟨7342713110897444058769381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9790284147863258745025841 7342713110897444058769381)
                  ·
                    refine ⟨1376758708293270761019259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7342713110897444058769381 1376758708293270761019259)
                    ·
                      rfl

theorem cell23_8043684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 3, 2, 1, 2, 4].length) (baseStart_8043684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043684 prefixEnd_8043684 := by exact prefixLift 8043684
  have htrace : WordTrace (prefixWord ++ tailWord_8043684) baseStart_8043684 baseEnd_8043684 := by
    simpa [prefixWord, tailWord_8043684, baseEnd_8043684] using wordTrace_append hprefix tailTrace_8043684
  have hstable : (prefixWord ++ tailWord_8043684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043684).length < 2 ^ (prefixWord ++ tailWord_8043684).sum := by decide
  have hdescent : baseEnd_8043684 < baseStart_8043684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043718 : List Nat := [6, 1, 2, 2, 1, 1, 2, 2, 2, 4]
def baseStart_8043718 : Nat := 118140960795 + 8043718 * 2 ^ 59
def prefixEnd_8043718 : Nat := 4983230072969 + 3 ^ 40 * 8043718 * 2
def baseEnd_8043718 : Nat := 1376764527740688383344207

theorem tailTrace_8043718 : CollatzResearch.WordTrace tailWord_8043718 prefixEnd_8043718 1376764527740688383344207 := by
  unfold tailWord_8043718
  simp only [CollatzResearch.WordTrace]
  refine ⟨9168078046030966203408619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 195585664981993945672717205 9168078046030966203408619)
  ·
    refine ⟨13752117069046449305112929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9168078046030966203408619 13752117069046449305112929)
    ·
      refine ⟨10314087801784836978834697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13752117069046449305112929 10314087801784836978834697)
      ·
        refine ⟨7735565851338627734126023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10314087801784836978834697 7735565851338627734126023)
        ·
          refine ⟨11603348777007941601189035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7735565851338627734126023 11603348777007941601189035)
          ·
            refine ⟨17405023165511912401783553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11603348777007941601189035 17405023165511912401783553)
            ·
              refine ⟨13053767374133934301337665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17405023165511912401783553 13053767374133934301337665)
              ·
                refine ⟨9790325530600450726003249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13053767374133934301337665 9790325530600450726003249)
                ·
                  refine ⟨7342744147950338044502437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9790325530600450726003249 7342744147950338044502437)
                  ·
                    refine ⟨1376764527740688383344207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7342744147950338044502437 1376764527740688383344207)
                    ·
                      rfl

theorem cell23_8043718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_8043718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043718 prefixEnd_8043718 := by exact prefixLift 8043718
  have htrace : WordTrace (prefixWord ++ tailWord_8043718) baseStart_8043718 baseEnd_8043718 := by
    simpa [prefixWord, tailWord_8043718, baseEnd_8043718] using wordTrace_append hprefix tailTrace_8043718
  have hstable : (prefixWord ++ tailWord_8043718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043718).length < 2 ^ (prefixWord ++ tailWord_8043718).sum := by decide
  have hdescent : baseEnd_8043718 < baseStart_8043718 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043725 : List Nat := [1, 6, 2, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_8043725 : Nat := 118140960795 + 8043725 * 2 ^ 59
def prefixEnd_8043725 : Nat := 4983230072969 + 3 ^ 40 * 8043725 * 2
def baseEnd_8043725 : Nat := 4130297177586646622645089

theorem tailTrace_8043725 : CollatzResearch.WordTrace tailWord_8043725 prefixEnd_8043725 4130297177586646622645089 := by
  unfold tailWord_8043725
  simp only [CollatzResearch.WordTrace]
  refine ⟨293378752783965558704580629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195585835189310372469720419 293378752783965558704580629)
  ·
    refine ⟨13752129036748385564277217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 293378752783965558704580629 13752129036748385564277217)
    ·
      refine ⟨10314096777561289173207913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13752129036748385564277217 10314096777561289173207913)
      ·
        refine ⟨7735572583170966879905935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10314096777561289173207913 7735572583170966879905935)
        ·
          refine ⟨11603358874756450319858903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7735572583170966879905935 11603358874756450319858903)
          ·
            refine ⟨17405038312134675479788355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11603358874756450319858903 17405038312134675479788355)
            ·
              refine ⟨26107557468202013219682533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17405038312134675479788355 26107557468202013219682533)
              ·
                refine ⟨4895167025287877478690475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26107557468202013219682533 4895167025287877478690475)
                ·
                  refine ⟨7342750537931816218035713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4895167025287877478690475 7342750537931816218035713)
                  ·
                    refine ⟨5507062903448862163526785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7342750537931816218035713 5507062903448862163526785)
                    ·
                      refine ⟨4130297177586646622645089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5507062903448862163526785 4130297177586646622645089)
                      ·
                        rfl

theorem cell23_8043725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_8043725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043725 prefixEnd_8043725 := by exact prefixLift 8043725
  have htrace : WordTrace (prefixWord ++ tailWord_8043725) baseStart_8043725 baseEnd_8043725 := by
    simpa [prefixWord, tailWord_8043725, baseEnd_8043725] using wordTrace_append hprefix tailTrace_8043725
  have hstable : (prefixWord ++ tailWord_8043725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043725).length < 2 ^ (prefixWord ++ tailWord_8043725).sum := by decide
  have hdescent : baseEnd_8043725 < baseStart_8043725 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043743 : List Nat := [1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 4]
def baseStart_8043743 : Nat := 118140960795 + 8043743 * 2 ^ 59
def prefixEnd_8043743 : Nat := 4983230072969 + 3 ^ 40 * 8043743 * 2
def baseEnd_8043743 : Nat := 4130306420238427552220005

theorem tailTrace_8043743 : CollatzResearch.WordTrace tailWord_8043743 prefixEnd_8043743 4130306420238427552220005 := by
  unfold tailWord_8043743
  simp only [CollatzResearch.WordTrace]
  refine ⟨293379409297900347778735883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195586272865266898519157255 293379409297900347778735883)
  ·
    refine ⟨440069113946850521668103825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293379409297900347778735883 440069113946850521668103825)
    ·
      refine ⟨330051835460137891251077869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440069113946850521668103825 330051835460137891251077869)
      ·
        refine ⟨123769438297551709219154201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330051835460137891251077869 123769438297551709219154201)
        ·
          refine ⟨92827078723163781914365651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123769438297551709219154201 92827078723163781914365651)
          ·
            refine ⟨139240618084745672871548477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92827078723163781914365651 139240618084745672871548477)
            ·
              refine ⟨52215231781779627326830679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139240618084745672871548477 52215231781779627326830679)
              ·
                refine ⟨78322847672669440990246019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52215231781779627326830679 78322847672669440990246019)
                ·
                  refine ⟨117484271509004161485369029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78322847672669440990246019 117484271509004161485369029)
                  ·
                    refine ⟨22028300907938280278506693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117484271509004161485369029 22028300907938280278506693)
                    ·
                      refine ⟨4130306420238427552220005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22028300907938280278506693 4130306420238427552220005)
                      ·
                        rfl

theorem cell23_8043743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 1, 1, 4, 4].length) (baseStart_8043743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043743 prefixEnd_8043743 := by exact prefixLift 8043743
  have htrace : WordTrace (prefixWord ++ tailWord_8043743) baseStart_8043743 baseEnd_8043743 := by
    simpa [prefixWord, tailWord_8043743, baseEnd_8043743] using wordTrace_append hprefix tailTrace_8043743
  have hstable : (prefixWord ++ tailWord_8043743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043743).length < 2 ^ (prefixWord ++ tailWord_8043743).sum := by decide
  have hdescent : baseEnd_8043743 < baseStart_8043743 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043793 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 7]
def baseStart_8043793 : Nat := 118140960795 + 8043793 * 2 ^ 59
def prefixEnd_8043793 : Nat := 4983230072969 + 3 ^ 40 * 8043793 * 2
def baseEnd_8043793 : Nat := 4130332094271152356594775

theorem tailTrace_8043793 : CollatzResearch.WordTrace tailWord_8043793 prefixEnd_8043793 4130332094271152356594775 := by
  unfold tailWord_8043793
  simp only [CollatzResearch.WordTrace]
  refine ⟨293381232947719206318056033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195587488631812804212037355 293381232947719206318056033)
  ·
    refine ⟨220035924710789404738542025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293381232947719206318056033 220035924710789404738542025)
    ·
      refine ⟨165026943533092053553906519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220035924710789404738542025 165026943533092053553906519)
      ·
        refine ⟨247540415299638080330859779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165026943533092053553906519 247540415299638080330859779)
        ·
          refine ⟨371310622949457120496289669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247540415299638080330859779 371310622949457120496289669)
          ·
            refine ⟨69620741803023210093054313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 371310622949457120496289669 69620741803023210093054313)
            ·
              refine ⟨52215556352267407569790735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69620741803023210093054313 52215556352267407569790735)
              ·
                refine ⟨78323334528401111354686103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52215556352267407569790735 78323334528401111354686103)
                ·
                  refine ⟨117485001792601667032029155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78323334528401111354686103 117485001792601667032029155)
                  ·
                    refine ⟨176227502688902500548043733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117485001792601667032029155 176227502688902500548043733)
                    ·
                      refine ⟨4130332094271152356594775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176227502688902500548043733 4130332094271152356594775)
                      ·
                        rfl

theorem cell23_8043793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 7].length) (baseStart_8043793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043793 prefixEnd_8043793 := by exact prefixLift 8043793
  have htrace : WordTrace (prefixWord ++ tailWord_8043793) baseStart_8043793 baseEnd_8043793 := by
    simpa [prefixWord, tailWord_8043793, baseEnd_8043793] using wordTrace_append hprefix tailTrace_8043793
  have hstable : (prefixWord ++ tailWord_8043793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043793).length < 2 ^ (prefixWord ++ tailWord_8043793).sum := by decide
  have hdescent : baseEnd_8043793 < baseStart_8043793 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043820 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 4]
def baseStart_8043820 : Nat := 118140960795 + 8043820 * 2 ^ 59
def prefixEnd_8043820 : Nat := 4983230072969 + 3 ^ 40 * 8043820 * 2
def baseEnd_8043820 : Nat := 4130345958248823750957151

theorem tailTrace_8043820 : CollatzResearch.WordTrace tailWord_8043820 prefixEnd_8043820 4130345958248823750957151 := by
  unfold tailWord_8043820
  simp only [CollatzResearch.WordTrace]
  refine ⟨146691108859310694964644457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195588145145747593286192609 146691108859310694964644457)
  ·
    refine ⟨110018331644483021223483343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146691108859310694964644457 110018331644483021223483343)
    ·
      refine ⟨165027497466724531835225015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110018331644483021223483343 165027497466724531835225015)
      ·
        refine ⟨247541246200086797752837523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165027497466724531835225015 247541246200086797752837523)
        ·
          refine ⟨371311869300130196629256285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247541246200086797752837523 371311869300130196629256285)
          ·
            refine ⟨139241950987548823735971107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371311869300130196629256285 139241950987548823735971107)
            ·
              refine ⟨208862926481323235603956661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139241950987548823735971107 208862926481323235603956661)
              ·
                refine ⟨19580899357624053337870937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208862926481323235603956661 19580899357624053337870937)
                ·
                  refine ⟨14685674518218040003403203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19580899357624053337870937 14685674518218040003403203)
                  ·
                    refine ⟨22028511777327060005104805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14685674518218040003403203 22028511777327060005104805)
                    ·
                      refine ⟨4130345958248823750957151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22028511777327060005104805 4130345958248823750957151)
                      ·
                        rfl

theorem cell23_8043820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_8043820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043820 prefixEnd_8043820 := by exact prefixLift 8043820
  have htrace : WordTrace (prefixWord ++ tailWord_8043820) baseStart_8043820 baseEnd_8043820 := by
    simpa [prefixWord, tailWord_8043820, baseEnd_8043820] using wordTrace_append hprefix tailTrace_8043820
  have hstable : (prefixWord ++ tailWord_8043820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043820).length < 2 ^ (prefixWord ++ tailWord_8043820).sum := by decide
  have hdescent : baseEnd_8043820 < baseStart_8043820 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043821 : List Nat := [1, 5, 3, 1, 1, 3, 1, 3, 5]
def baseStart_8043821 : Nat := 118140960795 + 8043821 * 2 ^ 59
def prefixEnd_8043821 : Nat := 4983230072969 + 3 ^ 40 * 8043821 * 2
def baseEnd_8043821 : Nat := 458927385747719805227183

theorem tailTrace_8043821 : CollatzResearch.WordTrace tailWord_8043821 prefixEnd_8043821 458927385747719805227183 := by
  unfold tailWord_8043821
  simp only [CollatzResearch.WordTrace]
  refine ⟨293382254191617767100075317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195588169461078511400050211 293382254191617767100075317)
  ·
    refine ⟨27504586330464165665632061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293382254191617767100075317 27504586330464165665632061)
    ·
      refine ⟨10314219873924062124612023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 27504586330464165665632061 10314219873924062124612023)
      ·
        refine ⟨15471329810886093186918035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10314219873924062124612023 15471329810886093186918035)
        ·
          refine ⟨23206994716329139780377053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15471329810886093186918035 23206994716329139780377053)
          ·
            refine ⟨8702623018623427417641395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23206994716329139780377053 8702623018623427417641395)
            ·
              refine ⟨13053934527935141126462093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8702623018623427417641395 13053934527935141126462093)
              ·
                refine ⟨4895225447975677922423285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13053934527935141126462093 4895225447975677922423285)
                ·
                  refine ⟨458927385747719805227183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4895225447975677922423285 458927385747719805227183)
                  ·
                    rfl

theorem cell23_8043821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 1, 3, 5].length) (baseStart_8043821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043821 prefixEnd_8043821 := by exact prefixLift 8043821
  have htrace : WordTrace (prefixWord ++ tailWord_8043821) baseStart_8043821 baseEnd_8043821 := by
    simpa [prefixWord, tailWord_8043821, baseEnd_8043821] using wordTrace_append hprefix tailTrace_8043821
  have hstable : (prefixWord ++ tailWord_8043821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043821).length < 2 ^ (prefixWord ++ tailWord_8043821).sum := by decide
  have hdescent : baseEnd_8043821 < baseStart_8043821 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043823 : List Nat := [1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 5]
def baseStart_8043823 : Nat := 118140960795 + 8043823 * 2 ^ 59
def prefixEnd_8043823 : Nat := 4983230072969 + 3 ^ 40 * 8043823 * 2
def baseEnd_8043823 : Nat := 4130347498690787239219637

theorem tailTrace_8043823 : CollatzResearch.WordTrace tailWord_8043823 prefixEnd_8043823 4130347498690787239219637 := by
  unfold tailWord_8043823
  simp only [CollatzResearch.WordTrace]
  refine ⟨293382327137610521441648123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195588218091740347627765415 293382327137610521441648123)
  ·
    refine ⟨440073490706415782162472185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293382327137610521441648123 440073490706415782162472185)
    ·
      refine ⟨330055118029811836621854139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440073490706415782162472185 330055118029811836621854139)
      ·
        refine ⟨495082677044717754932781209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330055118029811836621854139 495082677044717754932781209)
        ·
          refine ⟨371312007783538316199585907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495082677044717754932781209 371312007783538316199585907)
          ·
            refine ⟨556968011675307474299378861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371312007783538316199585907 556968011675307474299378861)
            ·
              refine ⟨208863004378240302862267073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556968011675307474299378861 208863004378240302862267073)
              ·
                refine ⟨156647253283680227146700305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208863004378240302862267073 156647253283680227146700305)
                ·
                  refine ⟨117485439962760170360025229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156647253283680227146700305 117485439962760170360025229)
                  ·
                    refine ⟨44057039986035063885009461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117485439962760170360025229 44057039986035063885009461)
                    ·
                      refine ⟨4130347498690787239219637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44057039986035063885009461 4130347498690787239219637)
                      ·
                        rfl

theorem cell23_8043823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 5].length) (baseStart_8043823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043823 prefixEnd_8043823 := by exact prefixLift 8043823
  have htrace : WordTrace (prefixWord ++ tailWord_8043823) baseStart_8043823 baseEnd_8043823 := by
    simpa [prefixWord, tailWord_8043823, baseEnd_8043823] using wordTrace_append hprefix tailTrace_8043823
  have hstable : (prefixWord ++ tailWord_8043823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043823).length < 2 ^ (prefixWord ++ tailWord_8043823).sum := by decide
  have hdescent : baseEnd_8043823 < baseStart_8043823 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043847 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 3, 4]
def baseStart_8043847 : Nat := 118140960795 + 8043847 * 2 ^ 59
def prefixEnd_8043847 : Nat := 4983230072969 + 3 ^ 40 * 8043847 * 2
def baseEnd_8043847 : Nat := 1376786607408831715106509

theorem tailTrace_8043847 : CollatzResearch.WordTrace tailWord_8043847 prefixEnd_8043847 1376786607408831715106509 := by
  unfold tailWord_8043847
  simp only [CollatzResearch.WordTrace]
  refine ⟨293383202489523573540521795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195588801659682382360347863 293383202489523573540521795)
  ·
    refine ⟨440074803734285360310782693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293383202489523573540521795 440074803734285360310782693)
    ·
      refine ⟨82514025700178505058271755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440074803734285360310782693 82514025700178505058271755)
      ·
        refine ⟨123771038550267757587407633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82514025700178505058271755 123771038550267757587407633)
        ·
          refine ⟨92828278912700818190555725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123771038550267757587407633 92828278912700818190555725)
          ·
            refine ⟨34810604592262806821458397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92828278912700818190555725 34810604592262806821458397)
            ·
              refine ⟨13053976722098552558046899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34810604592262806821458397 13053976722098552558046899)
              ·
                refine ⟨19580965083147828837070349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13053976722098552558046899 19580965083147828837070349)
                ·
                  refine ⟨7342861906180435813901381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19580965083147828837070349 7342861906180435813901381)
                  ·
                    refine ⟨1376786607408831715106509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7342861906180435813901381 1376786607408831715106509)
                    ·
                      rfl

theorem cell23_8043847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 3, 4].length) (baseStart_8043847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043847 prefixEnd_8043847 := by exact prefixLift 8043847
  have htrace : WordTrace (prefixWord ++ tailWord_8043847) baseStart_8043847 baseEnd_8043847 := by
    simpa [prefixWord, tailWord_8043847, baseEnd_8043847] using wordTrace_append hprefix tailTrace_8043847
  have hstable : (prefixWord ++ tailWord_8043847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043847).length < 2 ^ (prefixWord ++ tailWord_8043847).sum := by decide
  have hdescent : baseEnd_8043847 < baseStart_8043847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043874 : List Nat := [3, 3, 2, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_8043874 : Nat := 118140960795 + 8043874 * 2 ^ 59
def prefixEnd_8043874 : Nat := 4983230072969 + 3 ^ 40 * 8043874 * 2
def baseEnd_8043874 : Nat := 4130373686204166539681903

theorem tailTrace_8043874 : CollatzResearch.WordTrace tailWord_8043874 prefixEnd_8043874 4130373686204166539681903 := by
  unfold tailWord_8043874
  simp only [CollatzResearch.WordTrace]
  refine ⟨73346046815106439287938669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195589458173617171434503117 73346046815106439287938669)
  ·
    refine ⟨27504767555664914732977001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73346046815106439287938669 27504767555664914732977001)
    ·
      refine ⟨20628575666748686049732751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27504767555664914732977001 20628575666748686049732751)
      ·
        refine ⟨30942863500123029074599127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20628575666748686049732751 30942863500123029074599127)
        ·
          refine ⟨46414295250184543611898691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30942863500123029074599127 46414295250184543611898691)
          ·
            refine ⟨69621442875276815417848037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46414295250184543611898691 69621442875276815417848037)
            ·
              refine ⟨13054020539114402890846507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69621442875276815417848037 13054020539114402890846507)
              ·
                refine ⟨19581030808671604336269761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13054020539114402890846507 19581030808671604336269761)
                ·
                  refine ⟨14685773106503703252202321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19581030808671604336269761 14685773106503703252202321)
                  ·
                    refine ⟨11014329829877777439151741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14685773106503703252202321 11014329829877777439151741)
                    ·
                      refine ⟨4130373686204166539681903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11014329829877777439151741 4130373686204166539681903)
                      ·
                        rfl

theorem cell23_8043874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_8043874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043874 prefixEnd_8043874 := by exact prefixLift 8043874
  have htrace : WordTrace (prefixWord ++ tailWord_8043874) baseStart_8043874 baseEnd_8043874 := by
    simpa [prefixWord, tailWord_8043874, baseEnd_8043874] using wordTrace_append hprefix tailTrace_8043874
  have hstable : (prefixWord ++ tailWord_8043874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043874).length < 2 ^ (prefixWord ++ tailWord_8043874).sum := by decide
  have hdescent : baseEnd_8043874 < baseStart_8043874 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043927 : List Nat := [1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 4]
def baseStart_8043927 : Nat := 118140960795 + 8043927 * 2 ^ 59
def prefixEnd_8043927 : Nat := 4983230072969 + 3 ^ 40 * 8043927 * 2
def baseEnd_8043927 : Nat := 4130400900678854832319159

theorem tailTrace_8043927 : CollatzResearch.WordTrace tailWord_8043927 prefixEnd_8043927 4130400900678854832319159 := by
  unfold tailWord_8043927
  simp only [CollatzResearch.WordTrace]
  refine ⟨293386120329233747203434035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195590746886155831468956023 293386120329233747203434035)
  ·
    refine ⟨440079180493850620805151053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293386120329233747203434035 440079180493850620805151053)
    ·
      refine ⟨165029692685193982801931645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440079180493850620805151053 165029692685193982801931645)
      ·
        refine ⟨61886134756947743550724367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165029692685193982801931645 61886134756947743550724367)
        ·
          refine ⟨92829202135421615326086551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61886134756947743550724367 92829202135421615326086551)
          ·
            refine ⟨139243803203132422989129827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92829202135421615326086551 139243803203132422989129827)
            ·
              refine ⟨208865704804698634483694741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139243803203132422989129827 208865704804698634483694741)
              ·
                refine ⟨9790579912720248491423191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208865704804698634483694741 9790579912720248491423191)
                ·
                  refine ⟨14685869869080372737134787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9790579912720248491423191 14685869869080372737134787)
                  ·
                    refine ⟨22028804803620559105702181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14685869869080372737134787 22028804803620559105702181)
                    ·
                      refine ⟨4130400900678854832319159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22028804803620559105702181 4130400900678854832319159)
                      ·
                        rfl

theorem cell23_8043927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_8043927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043927 prefixEnd_8043927 := by exact prefixLift 8043927
  have htrace : WordTrace (prefixWord ++ tailWord_8043927) baseStart_8043927 baseEnd_8043927 := by
    simpa [prefixWord, tailWord_8043927, baseEnd_8043927] using wordTrace_append hprefix tailTrace_8043927
  have hstable : (prefixWord ++ tailWord_8043927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043927).length < 2 ^ (prefixWord ++ tailWord_8043927).sum := by decide
  have hdescent : baseEnd_8043927 < baseStart_8043927 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043938 : List Nat := [3, 3, 1, 2, 1, 3, 2, 3, 1, 1, 3]
def baseStart_8043938 : Nat := 118140960795 + 8043938 * 2 ^ 59
def prefixEnd_8043938 : Nat := 4983230072969 + 3 ^ 40 * 8043938 * 2
def baseEnd_8043938 : Nat := 4130406548966054289281609

theorem tailTrace_8043938 : CollatzResearch.WordTrace tailWord_8043938 prefixEnd_8043938 4130406548966054289281609 := by
  unfold tailWord_8043938
  simp only [CollatzResearch.WordTrace]
  refine ⟨73346630383048474020521117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195591014354795930721389645 73346630383048474020521117)
  ·
    refine ⟨27504986393643177757695419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73346630383048474020521117 27504986393643177757695419)
    ·
      refine ⟨41257479590464766636543129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27504986393643177757695419 41257479590464766636543129)
      ·
        refine ⟨30943109692848574977407347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41257479590464766636543129 30943109692848574977407347)
        ·
          refine ⟨46414664539272862466111021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30943109692848574977407347 46414664539272862466111021)
          ·
            refine ⟨17405499202227323424791633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46414664539272862466111021 17405499202227323424791633)
            ·
              refine ⟨13054124401670492568593725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17405499202227323424791633 13054124401670492568593725)
              ·
                refine ⟨4895296650626434713222647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13054124401670492568593725 4895296650626434713222647)
                ·
                  refine ⟨7342944975939652069833971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4895296650626434713222647 7342944975939652069833971)
                  ·
                    refine ⟨11014417463909478104750957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7342944975939652069833971 11014417463909478104750957)
                    ·
                      refine ⟨4130406548966054289281609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11014417463909478104750957 4130406548966054289281609)
                      ·
                        rfl

theorem cell23_8043938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_8043938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043938 prefixEnd_8043938 := by exact prefixLift 8043938
  have htrace : WordTrace (prefixWord ++ tailWord_8043938) baseStart_8043938 baseEnd_8043938 := by
    simpa [prefixWord, tailWord_8043938, baseEnd_8043938] using wordTrace_append hprefix tailTrace_8043938
  have hstable : (prefixWord ++ tailWord_8043938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043938).length < 2 ^ (prefixWord ++ tailWord_8043938).sum := by decide
  have hdescent : baseEnd_8043938 < baseStart_8043938 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043940 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 3, 1, 6]
def baseStart_8043940 : Nat := 118140960795 + 8043940 * 2 ^ 59
def prefixEnd_8043940 : Nat := 4983230072969 + 3 ^ 40 * 8043940 * 2
def baseEnd_8043940 : Nat := 4130407575927363281456599

theorem tailTrace_8043940 : CollatzResearch.WordTrace tailWord_8043940 prefixEnd_8043940 4130407575927363281456599 := by
  unfold tailWord_8043940
  simp only [CollatzResearch.WordTrace]
  refine ⟨146693297239093325211828637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195591062985457766949104849 146693297239093325211828637)
  ·
    refine ⟨55009986464659996954435739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146693297239093325211828637 55009986464659996954435739)
    ·
      refine ⟨82514979696989995431653609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55009986464659996954435739 82514979696989995431653609)
      ·
        refine ⟨61886234772742496573740207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82514979696989995431653609 61886234772742496573740207)
        ·
          refine ⟨92829352159113744860610311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61886234772742496573740207 92829352159113744860610311)
          ·
            refine ⟨139244028238670617290915467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92829352159113744860610311 139244028238670617290915467)
            ·
              refine ⟨208866042358005925936373201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139244028238670617290915467 208866042358005925936373201)
              ·
                refine ⟨156649531768504444452279901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208866042358005925936373201 156649531768504444452279901)
                ·
                  refine ⟨58743574413189166669604963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156649531768504444452279901 58743574413189166669604963)
                  ·
                    refine ⟨88115361619783750004407445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58743574413189166669604963 88115361619783750004407445)
                    ·
                      refine ⟨4130407575927363281456599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88115361619783750004407445 4130407575927363281456599)
                      ·
                        rfl

theorem cell23_8043940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 3, 1, 6].length) (baseStart_8043940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043940 prefixEnd_8043940 := by exact prefixLift 8043940
  have htrace : WordTrace (prefixWord ++ tailWord_8043940) baseStart_8043940 baseEnd_8043940 := by
    simpa [prefixWord, tailWord_8043940, baseEnd_8043940] using wordTrace_append hprefix tailTrace_8043940
  have hstable : (prefixWord ++ tailWord_8043940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043940).length < 2 ^ (prefixWord ++ tailWord_8043940).sum := by decide
  have hdescent : baseEnd_8043940 < baseStart_8043940 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043964 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 1, 1, 5]
def baseStart_8043964 : Nat := 118140960795 + 8043964 * 2 ^ 59
def prefixEnd_8043964 : Nat := 4983230072969 + 3 ^ 40 * 8043964 * 2
def baseEnd_8043964 : Nat := 4130419899463071187556489

theorem tailTrace_8043964 : CollatzResearch.WordTrace tailWord_8043964 prefixEnd_8043964 4130419899463071187556489 := by
  unfold tailWord_8043964
  simp only [CollatzResearch.WordTrace]
  refine ⟨146693734915049851261265473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195591646553399801681687297 146693734915049851261265473)
  ·
    refine ⟨110020301186287388445949105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146693734915049851261265473 110020301186287388445949105)
    ·
      refine ⟨82515225889715541334461829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110020301186287388445949105 82515225889715541334461829)
      ·
        refine ⟨15471604854321664000211593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82515225889715541334461829 15471604854321664000211593)
        ·
          refine ⟨11603703640741248000158695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15471604854321664000211593 11603703640741248000158695)
          ·
            refine ⟨17405555461111872000238043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11603703640741248000158695 17405555461111872000238043)
            ·
              refine ⟨26108333191667808000357065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17405555461111872000238043 26108333191667808000357065)
              ·
                refine ⟨19581249893750856000267799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26108333191667808000357065 19581249893750856000267799)
                ·
                  refine ⟨29371874840626284000401699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19581249893750856000267799 29371874840626284000401699)
                  ·
                    refine ⟨44057812260939426000602549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29371874840626284000401699 44057812260939426000602549)
                    ·
                      refine ⟨4130419899463071187556489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44057812260939426000602549 4130419899463071187556489)
                      ·
                        rfl

theorem cell23_8043964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_8043964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043964 prefixEnd_8043964 := by exact prefixLift 8043964
  have htrace : WordTrace (prefixWord ++ tailWord_8043964) baseStart_8043964 baseEnd_8043964 := by
    simpa [prefixWord, tailWord_8043964, baseEnd_8043964] using wordTrace_append hprefix tailTrace_8043964
  have hstable : (prefixWord ++ tailWord_8043964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043964).length < 2 ^ (prefixWord ++ tailWord_8043964).sum := by decide
  have hdescent : baseEnd_8043964 < baseStart_8043964 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8043994 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3]
def baseStart_8043994 : Nat := 118140960795 + 8043994 * 2 ^ 59
def prefixEnd_8043994 : Nat := 4983230072969 + 3 ^ 40 * 8043994 * 2
def baseEnd_8043994 : Nat := 4130435303882706070181351

theorem tailTrace_8043994 : CollatzResearch.WordTrace tailWord_8043994 prefixEnd_8043994 4130435303882706070181351 := by
  unfold tailWord_8043994
  simp only [CollatzResearch.WordTrace]
  refine ⟨73347141004997754411530759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195592376013327345097415357 73347141004997754411530759)
  ·
    refine ⟨110020711507496631617296139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73347141004997754411530759 110020711507496631617296139)
    ·
      refine ⟨165031067261244947425944209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110020711507496631617296139 165031067261244947425944209)
      ·
        refine ⟨123773300445933710569458157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165031067261244947425944209 123773300445933710569458157)
        ·
          refine ⟨46414987667225141463546809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123773300445933710569458157 46414987667225141463546809)
          ·
            refine ⟨34811240750418856097660107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46414987667225141463546809 34811240750418856097660107)
            ·
              refine ⟨52216861125628284146490161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34811240750418856097660107 52216861125628284146490161)
              ·
                refine ⟨39162645844221213109867621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52216861125628284146490161 39162645844221213109867621)
                ·
                  refine ⟨7342996095791477458100179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39162645844221213109867621 7342996095791477458100179)
                  ·
                    refine ⟨11014494143687216187150269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7342996095791477458100179 11014494143687216187150269)
                    ·
                      refine ⟨4130435303882706070181351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11014494143687216187150269 4130435303882706070181351)
                      ·
                        rfl

theorem cell23_8043994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_8043994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8043994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8043994 prefixEnd_8043994 := by exact prefixLift 8043994
  have htrace : WordTrace (prefixWord ++ tailWord_8043994) baseStart_8043994 baseEnd_8043994 := by
    simpa [prefixWord, tailWord_8043994, baseEnd_8043994] using wordTrace_append hprefix tailTrace_8043994
  have hstable : (prefixWord ++ tailWord_8043994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8043994).length < 2 ^ (prefixWord ++ tailWord_8043994).sum := by decide
  have hdescent : baseEnd_8043994 < baseStart_8043994 := by decide
  rcases family_descends (prefixWord ++ tailWord_8043994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044144 : List Nat := [2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 3]
def baseStart_8044144 : Nat := 118140960795 + 8044144 * 2 ^ 59
def prefixEnd_8044144 : Nat := 4983230072969 + 3 ^ 40 * 8044144 * 2
def baseEnd_8044144 : Nat := 4130512325980880483305661

theorem tailTrace_8044144 : CollatzResearch.WordTrace tailWord_8044144 prefixEnd_8044144 4130512325980880483305661 := by
  unfold tailWord_8044144
  simp only [CollatzResearch.WordTrace]
  refine ⟨146697017484723796632041743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195596023312965062176055657 146697017484723796632041743)
  ·
    refine ⟨220045526227085694948062615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146697017484723796632041743 220045526227085694948062615)
    ·
      refine ⟨330068289340628542422093923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220045526227085694948062615 330068289340628542422093923)
      ·
        refine ⟨495102434010942813633140885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330068289340628542422093923 495102434010942813633140885)
        ·
          refine ⟨23207926594262944389053479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 495102434010942813633140885 23207926594262944389053479)
          ·
            refine ⟨34811889891394416583580219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23207926594262944389053479 34811889891394416583580219)
            ·
              refine ⟨52217834837091624875370329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34811889891394416583580219 52217834837091624875370329)
              ·
                refine ⟨39163376127818718656527747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52217834837091624875370329 39163376127818718656527747)
                ·
                  refine ⟨58745064191728077984791621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39163376127818718656527747 58745064191728077984791621)
                  ·
                    refine ⟨11014699535949014622148429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58745064191728077984791621 11014699535949014622148429)
                    ·
                      refine ⟨4130512325980880483305661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11014699535949014622148429 4130512325980880483305661)
                      ·
                        rfl

theorem cell23_8044144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 4, 3].length) (baseStart_8044144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044144 prefixEnd_8044144 := by exact prefixLift 8044144
  have htrace : WordTrace (prefixWord ++ tailWord_8044144) baseStart_8044144 baseEnd_8044144 := by
    simpa [prefixWord, tailWord_8044144, baseEnd_8044144] using wordTrace_append hprefix tailTrace_8044144
  have hstable : (prefixWord ++ tailWord_8044144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044144).length < 2 ^ (prefixWord ++ tailWord_8044144).sum := by decide
  have hdescent : baseEnd_8044144 < baseStart_8044144 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044178 : List Nat := [3, 2, 3, 1, 3, 1, 1, 2, 2, 2, 3]
def baseStart_8044178 : Nat := 118140960795 + 8044178 * 2 ^ 59
def prefixEnd_8044178 : Nat := 4983230072969 + 3 ^ 40 * 8044178 * 2
def baseEnd_8044178 : Nat := 4130529784323133350280505

theorem tailTrace_8044178 : CollatzResearch.WordTrace tailWord_8044178 prefixEnd_8044178 4130529784323133350280505 := by
  unfold tailWord_8044178
  simp only [CollatzResearch.WordTrace]
  refine ⟨73348818762831104267705297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195596850034216278047214125 73348818762831104267705297)
  ·
    refine ⟨55011614072123328200778973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73348818762831104267705297 55011614072123328200778973)
    ·
      refine ⟨20629355277046248075292115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55011614072123328200778973 20629355277046248075292115)
      ·
        refine ⟨30944032915569372112938173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20629355277046248075292115 30944032915569372112938173)
        ·
          refine ⟨11604012343338514542351815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30944032915569372112938173 11604012343338514542351815)
          ·
            refine ⟨17406018515007771813527723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11604012343338514542351815 17406018515007771813527723)
            ·
              refine ⟨26109027772511657720291585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17406018515007771813527723 26109027772511657720291585)
              ·
                refine ⟨19581770829383743290218689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26109027772511657720291585 19581770829383743290218689)
                ·
                  refine ⟨14686328122037807467664017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19581770829383743290218689 14686328122037807467664017)
                  ·
                    refine ⟨11014746091528355600748013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14686328122037807467664017 11014746091528355600748013)
                    ·
                      refine ⟨4130529784323133350280505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11014746091528355600748013 4130529784323133350280505)
                      ·
                        rfl

theorem cell23_8044178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_8044178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044178 prefixEnd_8044178 := by exact prefixLift 8044178
  have htrace : WordTrace (prefixWord ++ tailWord_8044178) baseStart_8044178 baseEnd_8044178 := by
    simpa [prefixWord, tailWord_8044178, baseEnd_8044178] using wordTrace_append hprefix tailTrace_8044178
  have hstable : (prefixWord ++ tailWord_8044178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044178).length < 2 ^ (prefixWord ++ tailWord_8044178).sum := by decide
  have hdescent : baseEnd_8044178 < baseStart_8044178 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044218 : List Nat := [3, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2]
def baseStart_8044218 : Nat := 118140960795 + 8044218 * 2 ^ 59
def prefixEnd_8044218 : Nat := 4983230072969 + 3 ^ 40 * 8044218 * 2
def baseEnd_8044218 : Nat := 4130550323549313193780321

theorem tailTrace_8044218 : CollatzResearch.WordTrace tailWord_8044218 prefixEnd_8044218 4130550323549313193780321 := by
  unfold tailWord_8044218
  simp only [CollatzResearch.WordTrace]
  refine ⟨73349183492794875975569327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195597822647453002601518205 73349183492794875975569327)
  ·
    refine ⟨110023775239192313963353991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73349183492794875975569327 110023775239192313963353991)
    ·
      refine ⟨165035662858788470945030987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110023775239192313963353991 165035662858788470945030987)
      ·
        refine ⟨247553494288182706417546481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165035662858788470945030987 247553494288182706417546481)
        ·
          refine ⟨185665120716137029813159861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247553494288182706417546481 185665120716137029813159861)
          ·
            refine ⟨17406105067137846544983737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185665120716137029813159861 17406105067137846544983737)
            ·
              refine ⟨13054578800353384908737803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17406105067137846544983737 13054578800353384908737803)
              ·
                refine ⟨19581868200530077363106705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13054578800353384908737803 19581868200530077363106705)
                ·
                  refine ⟨14686401150397558022330029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19581868200530077363106705 14686401150397558022330029)
                  ·
                    refine ⟨5507400431399084258373761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14686401150397558022330029 5507400431399084258373761)
                    ·
                      refine ⟨4130550323549313193780321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5507400431399084258373761 4130550323549313193780321)
                      ·
                        rfl

theorem cell23_8044218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 1, 2, 3, 2].length) (baseStart_8044218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044218 prefixEnd_8044218 := by exact prefixLift 8044218
  have htrace : WordTrace (prefixWord ++ tailWord_8044218) baseStart_8044218 baseEnd_8044218 := by
    simpa [prefixWord, tailWord_8044218, baseEnd_8044218] using wordTrace_append hprefix tailTrace_8044218
  have hstable : (prefixWord ++ tailWord_8044218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044218).length < 2 ^ (prefixWord ++ tailWord_8044218).sum := by decide
  have hdescent : baseEnd_8044218 < baseStart_8044218 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044224 : List Nat := [2, 1, 1, 2, 4, 1, 3, 2, 1, 6]
def baseStart_8044224 : Nat := 118140960795 + 8044224 * 2 ^ 59
def prefixEnd_8044224 : Nat := 4983230072969 + 3 ^ 40 * 8044224 * 2
def baseEnd_8044224 : Nat := 1376851134811080056768431

theorem tailTrace_8044224 : CollatzResearch.WordTrace tailWord_8044224 prefixEnd_8044224 1376851134811080056768431 := by
  unfold tailWord_8044224
  simp only [CollatzResearch.WordTrace]
  refine ⟨146698476404578883463497863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195597968539438511284663817 146698476404578883463497863)
  ·
    refine ⟨220047714606868325195246795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146698476404578883463497863 220047714606868325195246795)
    ·
      refine ⟨330071571910302487792870193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220047714606868325195246795 330071571910302487792870193)
      ·
        refine ⟨247553678932726865844652645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330071571910302487792870193 247553678932726865844652645)
        ·
          refine ⟨46416314799886287345872371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247553678932726865844652645 46416314799886287345872371)
          ·
            refine ⟨69624472199829431018808557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46416314799886287345872371 69624472199829431018808557)
            ·
              refine ⟨26109177074936036632053209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69624472199829431018808557 26109177074936036632053209)
              ·
                refine ⟨19581882806202027474039907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26109177074936036632053209 19581882806202027474039907)
                ·
                  refine ⟨29372824209303041211059861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19581882806202027474039907 29372824209303041211059861)
                  ·
                    refine ⟨1376851134811080056768431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29372824209303041211059861 1376851134811080056768431)
                    ·
                      rfl

theorem cell23_8044224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 2, 1, 6].length) (baseStart_8044224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044224 prefixEnd_8044224 := by exact prefixLift 8044224
  have htrace : WordTrace (prefixWord ++ tailWord_8044224) baseStart_8044224 baseEnd_8044224 := by
    simpa [prefixWord, tailWord_8044224, baseEnd_8044224] using wordTrace_append hprefix tailTrace_8044224
  have hstable : (prefixWord ++ tailWord_8044224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044224).length < 2 ^ (prefixWord ++ tailWord_8044224).sum := by decide
  have hdescent : baseEnd_8044224 < baseStart_8044224 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044227 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 6]
def baseStart_8044227 : Nat := 118140960795 + 8044227 * 2 ^ 59
def prefixEnd_8044227 : Nat := 4983230072969 + 3 ^ 40 * 8044227 * 2
def baseEnd_8044227 : Nat := 4130554944875203658567779

theorem tailTrace_8044227 : CollatzResearch.WordTrace tailWord_8044227 prefixEnd_8044227 4130554944875203658567779 := by
  unfold tailWord_8044227
  simp only [CollatzResearch.WordTrace]
  refine ⟨293397062228146898439354935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195598041485431265626236623 293397062228146898439354935)
  ·
    refine ⟨440095593342220347659032403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293397062228146898439354935 440095593342220347659032403)
    ·
      refine ⟨660143390013330521488548605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440095593342220347659032403 660143390013330521488548605)
      ·
        refine ⟨247553771254998945558205727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 660143390013330521488548605 247553771254998945558205727)
        ·
          refine ⟨371330656882498418337308591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247553771254998945558205727 371330656882498418337308591)
          ·
            refine ⟨556995985323747627505962887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371330656882498418337308591 556995985323747627505962887)
            ·
              refine ⟨835493977985621441258944331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 556995985323747627505962887 835493977985621441258944331)
              ·
                refine ⟨1253240966978432161888416497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 835493977985621441258944331 1253240966978432161888416497)
                ·
                  refine ⟨939930725233824121416312373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1253240966978432161888416497 939930725233824121416312373)
                  ·
                    refine ⟨88118505490671011382779285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 939930725233824121416312373 88118505490671011382779285)
                    ·
                      refine ⟨4130554944875203658567779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88118505490671011382779285 4130554944875203658567779)
                      ·
                        rfl

theorem cell23_8044227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_8044227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044227 prefixEnd_8044227 := by exact prefixLift 8044227
  have htrace : WordTrace (prefixWord ++ tailWord_8044227) baseStart_8044227 baseEnd_8044227 := by
    simpa [prefixWord, tailWord_8044227, baseEnd_8044227] using wordTrace_append hprefix tailTrace_8044227
  have hstable : (prefixWord ++ tailWord_8044227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044227).length < 2 ^ (prefixWord ++ tailWord_8044227).sum := by decide
  have hdescent : baseEnd_8044227 < baseStart_8044227 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044228 : List Nat := [2, 3, 3, 1, 1, 1, 5, 1, 1, 5]
def baseStart_8044228 : Nat := 118140960795 + 8044228 * 2 ^ 59
def prefixEnd_8044228 : Nat := 4983230072969 + 3 ^ 40 * 8044228 * 2
def baseEnd_8044228 : Nat := 1376851819451952718218425

theorem tailTrace_8044228 : CollatzResearch.WordTrace tailWord_8044228 prefixEnd_8044228 1376851819451952718218425 := by
  unfold tailWord_8044228
  simp only [CollatzResearch.WordTrace]
  refine ⟨146698549350571637805070669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195598065800762183740094225 146698549350571637805070669)
  ·
    refine ⟨55011956006464364176901501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146698549350571637805070669 55011956006464364176901501)
    ·
      refine ⟨20629483502424136566338063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55011956006464364176901501 20629483502424136566338063)
      ·
        refine ⟨30944225253636204849507095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20629483502424136566338063 30944225253636204849507095)
        ·
          refine ⟨46416337880454307274260643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30944225253636204849507095 46416337880454307274260643)
          ·
            refine ⟨69624506820681460911390965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46416337880454307274260643 69624506820681460911390965)
            ·
              refine ⟨6527297514438886960442903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 69624506820681460911390965 6527297514438886960442903)
              ·
                refine ⟨9790946271658330440664355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6527297514438886960442903 9790946271658330440664355)
                ·
                  refine ⟨14686419407487495660996533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9790946271658330440664355 14686419407487495660996533)
                  ·
                    refine ⟨1376851819451952718218425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14686419407487495660996533 1376851819451952718218425)
                    ·
                      rfl

theorem cell23_8044228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_8044228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044228 prefixEnd_8044228 := by exact prefixLift 8044228
  have htrace : WordTrace (prefixWord ++ tailWord_8044228) baseStart_8044228 baseEnd_8044228 := by
    simpa [prefixWord, tailWord_8044228, baseEnd_8044228] using wordTrace_append hprefix tailTrace_8044228
  have hstable : (prefixWord ++ tailWord_8044228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044228).length < 2 ^ (prefixWord ++ tailWord_8044228).sum := by decide
  have hdescent : baseEnd_8044228 < baseStart_8044228 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044241 : List Nat := [1, 2, 2, 1, 2, 4, 1, 4, 2, 4]
def baseStart_8044241 : Nat := 118140960795 + 8044241 * 2 ^ 59
def prefixEnd_8044241 : Nat := 4983230072969 + 3 ^ 40 * 8044241 * 2
def baseEnd_8044241 : Nat := 1376854044534788867930905

theorem tailTrace_8044241 : CollatzResearch.WordTrace tailWord_8044241 prefixEnd_8044241 1376854044534788867930905 := by
  unfold tailWord_8044241
  simp only [CollatzResearch.WordTrace]
  refine ⟨293397572850096178830364577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195598381900064119220243051 293397572850096178830364577)
  ·
    refine ⟨220048179637572134122773433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293397572850096178830364577 220048179637572134122773433)
    ·
      refine ⟨165036134728179100592080075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220048179637572134122773433 165036134728179100592080075)
      ·
        refine ⟨247554202092268650888120113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165036134728179100592080075 247554202092268650888120113)
        ·
          refine ⟨185665651569201488166090085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247554202092268650888120113 185665651569201488166090085)
          ·
            refine ⟨34812309669225279031141891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185665651569201488166090085 34812309669225279031141891)
            ·
              refine ⟨52218464503837918546712837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34812309669225279031141891 52218464503837918546712837)
              ·
                refine ⟨9790962094469609727508657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52218464503837918546712837 9790962094469609727508657)
                ·
                  refine ⟨7343221570852207295631493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9790962094469609727508657 7343221570852207295631493)
                  ·
                    refine ⟨1376854044534788867930905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7343221570852207295631493 1376854044534788867930905)
                    ·
                      rfl

theorem cell23_8044241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 1, 4, 2, 4].length) (baseStart_8044241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044241 prefixEnd_8044241 := by exact prefixLift 8044241
  have htrace : WordTrace (prefixWord ++ tailWord_8044241) baseStart_8044241 baseEnd_8044241 := by
    simpa [prefixWord, tailWord_8044241, baseEnd_8044241] using wordTrace_append hprefix tailTrace_8044241
  have hstable : (prefixWord ++ tailWord_8044241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044241).length < 2 ^ (prefixWord ++ tailWord_8044241).sum := by decide
  have hdescent : baseEnd_8044241 < baseStart_8044241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044242 : List Nat := [3, 2, 2, 2, 2, 1, 4, 2, 1, 1, 3]
def baseStart_8044242 : Nat := 118140960795 + 8044242 * 2 ^ 59
def prefixEnd_8044242 : Nat := 4983230072969 + 3 ^ 40 * 8044242 * 2
def baseEnd_8044242 : Nat := 4130562647085021099880211

theorem tailTrace_8044242 : CollatzResearch.WordTrace tailWord_8044242 prefixEnd_8044242 4130562647085021099880211 := by
  unfold tailWord_8044242
  simp only [CollatzResearch.WordTrace]
  refine ⟨73349402330773139000287745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195598406215395037334100653 73349402330773139000287745)
  ·
    refine ⟨55012051748079854250215809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73349402330773139000287745 55012051748079854250215809)
    ·
      refine ⟨41259038811059890687661857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55012051748079854250215809 41259038811059890687661857)
      ·
        refine ⟨30944279108294918015746393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41259038811059890687661857 30944279108294918015746393)
        ·
          refine ⟨23208209331221188511809795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30944279108294918015746393 23208209331221188511809795)
          ·
            refine ⟨34812313996831782767714693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23208209331221188511809795 34812313996831782767714693)
            ·
              refine ⟨6527308874405959268946505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34812313996831782767714693 6527308874405959268946505)
              ·
                refine ⟨4895481655804469451709879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6527308874405959268946505 4895481655804469451709879)
                ·
                  refine ⟨7343222483706704177564819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4895481655804469451709879 7343222483706704177564819)
                  ·
                    refine ⟨11014833725560056266347229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7343222483706704177564819 11014833725560056266347229)
                    ·
                      refine ⟨4130562647085021099880211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11014833725560056266347229 4130562647085021099880211)
                      ·
                        rfl

theorem cell23_8044242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 4, 2, 1, 1, 3].length) (baseStart_8044242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044242 prefixEnd_8044242 := by exact prefixLift 8044242
  have htrace : WordTrace (prefixWord ++ tailWord_8044242) baseStart_8044242 baseEnd_8044242 := by
    simpa [prefixWord, tailWord_8044242, baseEnd_8044242] using wordTrace_append hprefix tailTrace_8044242
  have hstable : (prefixWord ++ tailWord_8044242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044242).length < 2 ^ (prefixWord ++ tailWord_8044242).sum := by decide
  have hdescent : baseEnd_8044242 < baseStart_8044242 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044248 : List Nat := [2, 1, 2, 2, 3, 1, 2, 3, 3, 2, 2]
def baseStart_8044248 : Nat := 118140960795 + 8044248 * 2 ^ 59
def prefixEnd_8044248 : Nat := 4983230072969 + 3 ^ 40 * 8044248 * 2
def baseEnd_8044248 : Nat := 4130565727968948076405183

theorem tailTrace_8044248 : CollatzResearch.WordTrace tailWord_8044248 prefixEnd_8044248 4130565727968948076405183 := by
  unfold tailWord_8044248
  simp only [CollatzResearch.WordTrace]
  refine ⟨146698914080535409512934699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195598552107380546017246265 146698914080535409512934699)
  ·
    refine ⟨220048371120803114269402049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146698914080535409512934699 220048371120803114269402049)
    ·
      refine ⟨165036278340602335702051537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220048371120803114269402049 165036278340602335702051537)
      ·
        refine ⟨123777208755451751776538653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165036278340602335702051537 123777208755451751776538653)
        ·
          refine ⟨46416453283294406916201995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123777208755451751776538653 46416453283294406916201995)
          ·
            refine ⟨69624679924941610374302993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46416453283294406916201995 69624679924941610374302993)
            ·
              refine ⟨52218509943706207780727245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69624679924941610374302993 52218509943706207780727245)
              ·
                refine ⟨19581941228889827917772717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52218509943706207780727245 19581941228889827917772717)
                ·
                  refine ⟨7343227960833685469164769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19581941228889827917772717 7343227960833685469164769)
                  ·
                    refine ⟨5507420970625264101873577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7343227960833685469164769 5507420970625264101873577)
                    ·
                      refine ⟨4130565727968948076405183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5507420970625264101873577 4130565727968948076405183)
                      ·
                        rfl

theorem cell23_8044248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 3, 3, 2, 2].length) (baseStart_8044248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044248 prefixEnd_8044248 := by exact prefixLift 8044248
  have htrace : WordTrace (prefixWord ++ tailWord_8044248) baseStart_8044248 baseEnd_8044248 := by
    simpa [prefixWord, tailWord_8044248, baseEnd_8044248] using wordTrace_append hprefix tailTrace_8044248
  have hstable : (prefixWord ++ tailWord_8044248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044248).length < 2 ^ (prefixWord ++ tailWord_8044248).sum := by decide
  have hdescent : baseEnd_8044248 < baseStart_8044248 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044261 : List Nat := [1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 4]
def baseStart_8044261 : Nat := 118140960795 + 8044261 * 2 ^ 59
def prefixEnd_8044261 : Nat := 4983230072969 + 3 ^ 40 * 8044261 * 2
def baseEnd_8044261 : Nat := 4130572403217456525542623

theorem tailTrace_8044261 : CollatzResearch.WordTrace tailWord_8044261 prefixEnd_8044261 4130572403217456525542623 := by
  unfold tailWord_8044261
  simp only [CollatzResearch.WordTrace]
  refine ⟨293398302310023722246092637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195598868206682481497395091 293398302310023722246092637)
  ·
    refine ⟨110024363366258895842284739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293398302310023722246092637 110024363366258895842284739)
    ·
      refine ⟨165036545049388343763427109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110024363366258895842284739 165036545049388343763427109)
      ·
        refine ⟨30944352196760314455642583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165036545049388343763427109 30944352196760314455642583)
        ·
          refine ⟨46416528295140471683463875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30944352196760314455642583 46416528295140471683463875)
          ·
            refine ⟨69624792442710707525195813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46416528295140471683463875 69624792442710707525195813)
            ·
              refine ⟨13054648583008257660974215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69624792442710707525195813 13054648583008257660974215)
              ·
                refine ⟨19581972874512386491461323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13054648583008257660974215 19581972874512386491461323)
                ·
                  refine ⟨29372959311768579737191985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19581972874512386491461323 29372959311768579737191985)
                  ·
                    refine ⟨22029719483826434802893989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29372959311768579737191985 22029719483826434802893989)
                    ·
                      refine ⟨4130572403217456525542623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22029719483826434802893989 4130572403217456525542623)
                      ·
                        rfl

theorem cell23_8044261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_8044261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044261 prefixEnd_8044261 := by exact prefixLift 8044261
  have htrace : WordTrace (prefixWord ++ tailWord_8044261) baseStart_8044261 baseEnd_8044261 := by
    simpa [prefixWord, tailWord_8044261, baseEnd_8044261] using wordTrace_append hprefix tailTrace_8044261
  have hstable : (prefixWord ++ tailWord_8044261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044261).length < 2 ^ (prefixWord ++ tailWord_8044261).sum := by decide
  have hdescent : baseEnd_8044261 < baseStart_8044261 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044298 : List Nat := [3, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3]
def baseStart_8044298 : Nat := 118140960795 + 8044298 * 2 ^ 59
def prefixEnd_8044298 : Nat := 4983230072969 + 3 ^ 40 * 8044298 * 2
def baseEnd_8044298 : Nat := 4130591402001672880779953

theorem tailTrace_8044298 : CollatzResearch.WordTrace tailWord_8044298 prefixEnd_8044298 4130591402001672880779953 := by
  unfold tailWord_8044298
  simp only [CollatzResearch.WordTrace]
  refine ⟨73349912952722419391297387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195599767873926451710126365 73349912952722419391297387)
  ·
    refine ⟨110024869429083629086946081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73349912952722419391297387 110024869429083629086946081)
    ·
      refine ⟨82518652071812721815209561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110024869429083629086946081 82518652071812721815209561)
      ·
        refine ⟨61888989053859541361407171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82518652071812721815209561 61888989053859541361407171)
        ·
          refine ⟨92833483580789312042110757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61888989053859541361407171 92833483580789312042110757)
          ·
            refine ⟨17406278171397996007895767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92833483580789312042110757 17406278171397996007895767)
            ·
              refine ⟨26109417257096994011843651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17406278171397996007895767 26109417257096994011843651)
              ·
                refine ⟨39164125885645491017765477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26109417257096994011843651 39164125885645491017765477)
                ·
                  refine ⟨7343273603558529565831027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39164125885645491017765477 7343273603558529565831027)
                  ·
                    refine ⟨11014910405337794348746541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7343273603558529565831027 11014910405337794348746541)
                    ·
                      refine ⟨4130591402001672880779953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11014910405337794348746541 4130591402001672880779953)
                      ·
                        rfl

theorem cell23_8044298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 1, 1, 4, 1, 3].length) (baseStart_8044298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044298 prefixEnd_8044298 := by exact prefixLift 8044298
  have htrace : WordTrace (prefixWord ++ tailWord_8044298) baseStart_8044298 baseEnd_8044298 := by
    simpa [prefixWord, tailWord_8044298, baseEnd_8044298] using wordTrace_append hprefix tailTrace_8044298
  have hstable : (prefixWord ++ tailWord_8044298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044298).length < 2 ^ (prefixWord ++ tailWord_8044298).sum := by decide
  have hdescent : baseEnd_8044298 < baseStart_8044298 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044325 : List Nat := [1, 3, 1, 2, 3, 3, 2, 2, 1, 3, 2]
def baseStart_8044325 : Nat := 118140960795 + 8044325 * 2 ^ 59
def prefixEnd_8044325 : Nat := 4983230072969 + 3 ^ 40 * 8044325 * 2
def baseEnd_8044325 : Nat := 4130605265979344275142329

theorem tailTrace_8044325 : CollatzResearch.WordTrace tailWord_8044325 prefixEnd_8044325 4130605265979344275142329 := by
  unfold tailWord_8044325
  simp only [CollatzResearch.WordTrace]
  refine ⟨293400636581791861176422429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195600424387861240784281619 293400636581791861176422429)
  ·
    refine ⟨110025238718171947941158411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293400636581791861176422429 110025238718171947941158411)
    ·
      refine ⟨165037858077257921911737617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110025238718171947941158411 165037858077257921911737617)
      ·
        refine ⟨123778393557943441433803213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165037858077257921911737617 123778393557943441433803213)
        ·
          refine ⟨46416897584228790537676205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123778393557943441433803213 46416897584228790537676205)
          ·
            refine ⟨17406336594085796451628577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46416897584228790537676205 17406336594085796451628577)
            ·
              refine ⟨13054752445564347338721433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17406336594085796451628577 13054752445564347338721433)
              ·
                refine ⟨9791064334173260504041075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13054752445564347338721433 9791064334173260504041075)
                ·
                  refine ⟨14686596501259890756061613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9791064334173260504041075 14686596501259890756061613)
                  ·
                    refine ⟨5507473687972459033523105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14686596501259890756061613 5507473687972459033523105)
                    ·
                      refine ⟨4130605265979344275142329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5507473687972459033523105 4130605265979344275142329)
                      ·
                        rfl

theorem cell23_8044325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 3, 2].length) (baseStart_8044325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044325 prefixEnd_8044325 := by exact prefixLift 8044325
  have htrace : WordTrace (prefixWord ++ tailWord_8044325) baseStart_8044325 baseEnd_8044325 := by
    simpa [prefixWord, tailWord_8044325, baseEnd_8044325] using wordTrace_append hprefix tailTrace_8044325
  have hstable : (prefixWord ++ tailWord_8044325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044325).length < 2 ^ (prefixWord ++ tailWord_8044325).sum := by decide
  have hdescent : baseEnd_8044325 < baseStart_8044325 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044342 : List Nat := [5, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2]
def baseStart_8044342 : Nat := 118140960795 + 8044342 * 2 ^ 59
def prefixEnd_8044342 : Nat := 4983230072969 + 3 ^ 40 * 8044342 * 2
def baseEnd_8044342 : Nat := 4130613995150470708629751

theorem tailTrace_8044342 : CollatzResearch.WordTrace tailWord_8044342 prefixEnd_8044342 4130613995150470708629751 := by
  unfold tailWord_8044342
  simp only [CollatzResearch.WordTrace]
  refine ⟨18337578538920642067486955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195600837748486848719860853 18337578538920642067486955)
  ·
    refine ⟨27506367808380963101230433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18337578538920642067486955 27506367808380963101230433)
    ·
      refine ⟨20629775856285722325922825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27506367808380963101230433 20629775856285722325922825)
      ·
        refine ⟨15472331892214291744442119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20629775856285722325922825 15472331892214291744442119)
        ·
          refine ⟨23208497838321437616663179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15472331892214291744442119 23208497838321437616663179)
          ·
            refine ⟨34812746757482156424994769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23208497838321437616663179 34812746757482156424994769)
            ·
              refine ⟨26109560068111617318746077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34812746757482156424994769 26109560068111617318746077)
              ·
                refine ⟨9791085025541856494529779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26109560068111617318746077 9791085025541856494529779)
                ·
                  refine ⟨14686627538312784741794669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9791085025541856494529779 14686627538312784741794669)
                  ·
                    refine ⟨5507485326867294278173001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14686627538312784741794669 5507485326867294278173001)
                    ·
                      refine ⟨4130613995150470708629751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5507485326867294278173001 4130613995150470708629751)
                      ·
                        rfl

theorem cell23_8044342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_8044342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044342 prefixEnd_8044342 := by exact prefixLift 8044342
  have htrace : WordTrace (prefixWord ++ tailWord_8044342) baseStart_8044342 baseEnd_8044342 := by
    simpa [prefixWord, tailWord_8044342, baseEnd_8044342] using wordTrace_append hprefix tailTrace_8044342
  have hstable : (prefixWord ++ tailWord_8044342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044342).length < 2 ^ (prefixWord ++ tailWord_8044342).sum := by decide
  have hdescent : baseEnd_8044342 < baseStart_8044342 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044372 : List Nat := [2, 4, 1, 1, 3, 2, 1, 3, 2, 2, 2]
def baseStart_8044372 : Nat := 118140960795 + 8044372 * 2 ^ 59
def prefixEnd_8044372 : Nat := 4983230072969 + 3 ^ 40 * 8044372 * 2
def baseEnd_8044372 : Nat := 4130629399570105591254613

theorem tailTrace_8044372 : CollatzResearch.WordTrace tailWord_8044372 prefixEnd_8044372 4130629399570105591254613 := by
  unfold tailWord_8044372
  simp only [CollatzResearch.WordTrace]
  refine ⟨146701175406310794101691685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195601567208414392135588913 146701175406310794101691685)
  ·
    refine ⟨27506470388683273894067191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146701175406310794101691685 27506470388683273894067191)
    ·
      refine ⟨41259705583024910841100787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27506470388683273894067191 41259705583024910841100787)
      ·
        refine ⟨61889558374537366261651181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41259705583024910841100787 61889558374537366261651181)
        ·
          refine ⟨23208584390451512348119193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61889558374537366261651181 23208584390451512348119193)
          ·
            refine ⟨17406438292838634261089395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23208584390451512348119193 17406438292838634261089395)
            ·
              refine ⟨26109657439257951391634093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17406438292838634261089395 26109657439257951391634093)
              ·
                refine ⟨9791121539721731771862785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26109657439257951391634093 9791121539721731771862785)
                ·
                  refine ⟨7343341154791298828897089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9791121539721731771862785 7343341154791298828897089)
                  ·
                    refine ⟨5507505866093474121672817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7343341154791298828897089 5507505866093474121672817)
                    ·
                      refine ⟨4130629399570105591254613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5507505866093474121672817 4130629399570105591254613)
                      ·
                        rfl

theorem cell23_8044372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 1, 3, 2, 2, 2].length) (baseStart_8044372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044372 prefixEnd_8044372 := by exact prefixLift 8044372
  have htrace : WordTrace (prefixWord ++ tailWord_8044372) baseStart_8044372 baseEnd_8044372 := by
    simpa [prefixWord, tailWord_8044372, baseEnd_8044372] using wordTrace_append hprefix tailTrace_8044372
  have hstable : (prefixWord ++ tailWord_8044372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044372).length < 2 ^ (prefixWord ++ tailWord_8044372).sum := by decide
  have hdescent : baseEnd_8044372 < baseStart_8044372 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044445 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_8044445 : Nat := 118140960795 + 8044445 * 2 ^ 59
def prefixEnd_8044445 : Nat := 4983230072969 + 3 ^ 40 * 8044445 * 2
def baseEnd_8044445 : Nat := 4130666883657883805641777

theorem tailTrace_8044445 : CollatzResearch.WordTrace tailWord_8044445 prefixEnd_8044445 4130666883657883805641777 := by
  unfold tailWord_8044445
  simp only [CollatzResearch.WordTrace]
  refine ⟨293405013341357121670790789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195603342227571414447193859 293405013341357121670790789)
  ·
    refine ⟨55013440001504460313273273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293405013341357121670790789 55013440001504460313273273)
    ·
      refine ⟨41260080001128345234954955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55013440001504460313273273 41260080001128345234954955)
      ·
        refine ⟨61890120001692517852432433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41260080001128345234954955 61890120001692517852432433)
        ·
          refine ⟨46417590001269388389324325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61890120001692517852432433 46417590001269388389324325)
          ·
            refine ⟨8703298125238010322998311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46417590001269388389324325 8703298125238010322998311)
            ·
              refine ⟨13054947187857015484497467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8703298125238010322998311 13054947187857015484497467)
              ·
                refine ⟨19582420781785523226746201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13054947187857015484497467 19582420781785523226746201)
                ·
                  refine ⟨14686815586339142420059651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19582420781785523226746201 14686815586339142420059651)
                  ·
                    refine ⟨22030223379508713630089477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14686815586339142420059651 22030223379508713630089477)
                    ·
                      refine ⟨4130666883657883805641777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22030223379508713630089477 4130666883657883805641777)
                      ·
                        rfl

theorem cell23_8044445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_8044445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044445 prefixEnd_8044445 := by exact prefixLift 8044445
  have htrace : WordTrace (prefixWord ++ tailWord_8044445) baseStart_8044445 baseEnd_8044445 := by
    simpa [prefixWord, tailWord_8044445, baseEnd_8044445] using wordTrace_append hprefix tailTrace_8044445
  have hstable : (prefixWord ++ tailWord_8044445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044445).length < 2 ^ (prefixWord ++ tailWord_8044445).sum := by decide
  have hdescent : baseEnd_8044445 < baseStart_8044445 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044528 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 4, 4]
def baseStart_8044528 : Nat := 118140960795 + 8044528 * 2 ^ 59
def prefixEnd_8044528 : Nat := 4983230072969 + 3 ^ 40 * 8044528 * 2
def baseEnd_8044528 : Nat := 1376903167517402326967965

theorem tailTrace_8044528 : CollatzResearch.WordTrace tailWord_8044528 prefixEnd_8044528 1376903167517402326967965 := by
  unfold tailWord_8044528
  simp only [CollatzResearch.WordTrace]
  refine ⟨146704020300028213423031119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195605360400037617897374825 146704020300028213423031119)
  ·
    refine ⟨220056030450042320134546679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146704020300028213423031119 220056030450042320134546679)
    ·
      refine ⟨330084045675063480201820019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220056030450042320134546679 330084045675063480201820019)
      ·
        refine ⟨495126068512595220302730029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330084045675063480201820019 495126068512595220302730029)
        ·
          refine ⟨185672275692223207613523761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495126068512595220302730029 185672275692223207613523761)
          ·
            refine ⟨139254206769167405710142821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185672275692223207613523761 139254206769167405710142821)
            ·
              refine ⟨26110163769218888570651779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139254206769167405710142821 26110163769218888570651779)
              ·
                refine ⟨39165245653828332855977669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26110163769218888570651779 39165245653828332855977669)
                ·
                  refine ⟨7343483560092812410495813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39165245653828332855977669 7343483560092812410495813)
                  ·
                    refine ⟨1376903167517402326967965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7343483560092812410495813 1376903167517402326967965)
                    ·
                      rfl

theorem cell23_8044528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 4, 4].length) (baseStart_8044528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044528 prefixEnd_8044528 := by exact prefixLift 8044528
  have htrace : WordTrace (prefixWord ++ tailWord_8044528) baseStart_8044528 baseEnd_8044528 := by
    simpa [prefixWord, tailWord_8044528, baseEnd_8044528] using wordTrace_append hprefix tailTrace_8044528
  have hstable : (prefixWord ++ tailWord_8044528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044528).length < 2 ^ (prefixWord ++ tailWord_8044528).sum := by decide
  have hdescent : baseEnd_8044528 < baseStart_8044528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044529 : List Nat := [1, 2, 2, 2, 6, 1, 1, 1, 3, 1, 3]
def baseStart_8044529 : Nat := 118140960795 + 8044529 * 2 ^ 59
def prefixEnd_8044529 : Nat := 4983230072969 + 3 ^ 40 * 8044529 * 2
def baseEnd_8044529 : Nat := 4130710016032861476991391

theorem tailTrace_8044529 : CollatzResearch.WordTrace tailWord_8044529 prefixEnd_8044529 4130710016032861476991391 := by
  unfold tailWord_8044529
  simp only [CollatzResearch.WordTrace]
  refine ⟨293408077073052804016848641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195605384715368536011232427 293408077073052804016848641)
  ·
    refine ⟨220056057804789603012636481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293408077073052804016848641 220056057804789603012636481)
    ·
      refine ⟨165042043353592202259477361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220056057804789603012636481 165042043353592202259477361)
      ·
        refine ⟨123781532515194151694608021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165042043353592202259477361 123781532515194151694608021)
        ·
          refine ⟨5802259336649725860684751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123781532515194151694608021 5802259336649725860684751)
          ·
            refine ⟨8703389004974588791027127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5802259336649725860684751 8703389004974588791027127)
            ·
              refine ⟨13055083507461883186540691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8703389004974588791027127 13055083507461883186540691)
              ·
                refine ⟨19582625261192824779811037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13055083507461883186540691 19582625261192824779811037)
                ·
                  refine ⟨7343484472947309292429139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19582625261192824779811037 7343484472947309292429139)
                  ·
                    refine ⟨11015226709420963938643709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7343484472947309292429139 11015226709420963938643709)
                    ·
                      refine ⟨4130710016032861476991391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11015226709420963938643709 4130710016032861476991391)
                      ·
                        rfl

theorem cell23_8044529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_8044529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044529 prefixEnd_8044529 := by exact prefixLift 8044529
  have htrace : WordTrace (prefixWord ++ tailWord_8044529) baseStart_8044529 baseEnd_8044529 := by
    simpa [prefixWord, tailWord_8044529, baseEnd_8044529] using wordTrace_append hprefix tailTrace_8044529
  have hstable : (prefixWord ++ tailWord_8044529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044529).length < 2 ^ (prefixWord ++ tailWord_8044529).sum := by decide
  have hdescent : baseEnd_8044529 < baseStart_8044529 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044541 : List Nat := [1, 4, 1, 1, 1, 2, 3, 10]
def baseStart_8044541 : Nat := 118140960795 + 8044541 * 2 ^ 59
def prefixEnd_8044541 : Nat := 4983230072969 + 3 ^ 40 * 8044541 * 2
def baseEnd_8044541 : Nat := 152989488066693164075605

theorem tailTrace_8044541 : CollatzResearch.WordTrace tailWord_8044541 prefixEnd_8044541 152989488066693164075605 := by
  unfold tailWord_8044541
  simp only [CollatzResearch.WordTrace]
  refine ⟨293408514749009330066285477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195605676499339553377523651 293408514749009330066285477)
  ·
    refine ⟨55014096515439249387428527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293408514749009330066285477 55014096515439249387428527)
    ·
      refine ⟨82521144773158874081142791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55014096515439249387428527 82521144773158874081142791)
      ·
        refine ⟨123781717159738311121714187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82521144773158874081142791 123781717159738311121714187)
        ·
          refine ⟨185672575739607466682571281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123781717159738311121714187 185672575739607466682571281)
          ·
            refine ⟨139254431804705600011928461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185672575739607466682571281 139254431804705600011928461)
            ·
              refine ⟨52220411926764600004473173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139254431804705600011928461 52220411926764600004473173)
              ·
                refine ⟨152989488066693164075605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 52220411926764600004473173 152989488066693164075605)
                ·
                  rfl

theorem cell23_8044541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 3, 10].length) (baseStart_8044541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044541 prefixEnd_8044541 := by exact prefixLift 8044541
  have htrace : WordTrace (prefixWord ++ tailWord_8044541) baseStart_8044541 baseEnd_8044541 := by
    simpa [prefixWord, tailWord_8044541, baseEnd_8044541] using wordTrace_append hprefix tailTrace_8044541
  have hstable : (prefixWord ++ tailWord_8044541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044541).length < 2 ^ (prefixWord ++ tailWord_8044541).sum := by decide
  have hdescent : baseEnd_8044541 < baseStart_8044541 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044545 : List Nat := [1, 2, 4, 1, 2, 1, 3, 3, 2, 4]
def baseStart_8044545 : Nat := 118140960795 + 8044545 * 2 ^ 59
def prefixEnd_8044545 : Nat := 4983230072969 + 3 ^ 40 * 8044545 * 2
def baseEnd_8044545 : Nat := 1376906077241111138130439

theorem tailTrace_8044545 : CollatzResearch.WordTrace tailWord_8044545 prefixEnd_8044545 1376906077241111138130439 := by
  unfold tailWord_8044545
  simp only [CollatzResearch.WordTrace]
  refine ⟨293408660640994838749431089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195605773760663225832954059 293408660640994838749431089)
  ·
    refine ⟨220056495480746129062073317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293408660640994838749431089 220056495480746129062073317)
    ·
      refine ⟨41260592902639899199138747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220056495480746129062073317 41260592902639899199138747)
      ·
        refine ⟨61890889353959848798708121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41260592902639899199138747 61890889353959848798708121)
        ·
          refine ⟨46418167015469886599031091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61890889353959848798708121 46418167015469886599031091)
          ·
            refine ⟨69627250523204829898546637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46418167015469886599031091 69627250523204829898546637)
            ·
              refine ⟨26110218946201811211954989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69627250523204829898546637 26110218946201811211954989)
              ·
                refine ⟨9791332104825679204483121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26110218946201811211954989 9791332104825679204483121)
                ·
                  refine ⟨7343499078619259403362341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9791332104825679204483121 7343499078619259403362341)
                  ·
                    refine ⟨1376906077241111138130439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7343499078619259403362341 1376906077241111138130439)
                    ·
                      rfl

theorem cell23_8044545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_8044545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044545 prefixEnd_8044545 := by exact prefixLift 8044545
  have htrace : WordTrace (prefixWord ++ tailWord_8044545) baseStart_8044545 baseEnd_8044545 := by
    simpa [prefixWord, tailWord_8044545, baseEnd_8044545] using wordTrace_append hprefix tailTrace_8044545
  have hstable : (prefixWord ++ tailWord_8044545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044545).length < 2 ^ (prefixWord ++ tailWord_8044545).sum := by decide
  have hdescent : baseEnd_8044545 < baseStart_8044545 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044565 : List Nat := [1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 4]
def baseStart_8044565 : Nat := 118140960795 + 8044565 * 2 ^ 59
def prefixEnd_8044565 : Nat := 4983230072969 + 3 ^ 40 * 8044565 * 2
def baseEnd_8044565 : Nat := 4130728501336423336141225

theorem tailTrace_8044565 : CollatzResearch.WordTrace tailWord_8044565 prefixEnd_8044565 4130728501336423336141225 := by
  unfold tailWord_8044565
  simp only [CollatzResearch.WordTrace]
  refine ⟨293409390100922382165159149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195606260067281588110106099 293409390100922382165159149)
  ·
    refine ⟨110028521287845893311934681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293409390100922382165159149 110028521287845893311934681)
    ·
      refine ⟨82521390965884419983951011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110028521287845893311934681 82521390965884419983951011)
      ·
        refine ⟨123782086448826629975926517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82521390965884419983951011 123782086448826629975926517)
        ·
          refine ⟨11604570604577496560243111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123782086448826629975926517 11604570604577496560243111)
          ·
            refine ⟨17406855906866244840364667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11604570604577496560243111 17406855906866244840364667)
            ·
              refine ⟨26110283860299367260547001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17406855906866244840364667 26110283860299367260547001)
              ·
                refine ⟨19582712895224525445410251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26110283860299367260547001 19582712895224525445410251)
                ·
                  refine ⟨29374069342836788168115377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19582712895224525445410251 29374069342836788168115377)
                  ·
                    refine ⟨22030552007127591126086533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29374069342836788168115377 22030552007127591126086533)
                    ·
                      refine ⟨4130728501336423336141225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22030552007127591126086533 4130728501336423336141225)
                      ·
                        rfl

theorem cell23_8044565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_8044565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044565 prefixEnd_8044565 := by exact prefixLift 8044565
  have htrace : WordTrace (prefixWord ++ tailWord_8044565) baseStart_8044565 baseEnd_8044565 := by
    simpa [prefixWord, tailWord_8044565, baseEnd_8044565] using wordTrace_append hprefix tailTrace_8044565
  have hstable : (prefixWord ++ tailWord_8044565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044565).length < 2 ^ (prefixWord ++ tailWord_8044565).sum := by decide
  have hdescent : baseEnd_8044565 < baseStart_8044565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044586 : List Nat := [3, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_8044586 : Nat := 118140960795 + 8044586 * 2 ^ 59
def prefixEnd_8044586 : Nat := 4983230072969 + 3 ^ 40 * 8044586 * 2
def baseEnd_8044586 : Nat := 4130739284430167753978629

theorem tailTrace_8044586 : CollatzResearch.WordTrace tailWord_8044586 prefixEnd_8044586 4130739284430167753978629 := by
  unfold tailWord_8044586
  simp only [CollatzResearch.WordTrace]
  refine ⟨73352539008461575687918403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195606770689230868501115741 73352539008461575687918403)
  ·
    refine ⟨110028808512692363531877605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73352539008461575687918403 110028808512692363531877605)
    ·
      refine ⟨20630401596129818162227051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110028808512692363531877605 20630401596129818162227051)
      ·
        refine ⟨30945602394194727243340577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20630401596129818162227051 30945602394194727243340577)
        ·
          refine ⟨23209201795646045432505433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30945602394194727243340577 23209201795646045432505433)
          ·
            refine ⟨17406901346734534074379075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23209201795646045432505433 17406901346734534074379075)
            ·
              refine ⟨26110352020101801111568613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17406901346734534074379075 26110352020101801111568613)
              ·
                refine ⟨4895691003769087708419115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26110352020101801111568613 4895691003769087708419115)
                ·
                  refine ⟨7343536505653631562628673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4895691003769087708419115 7343536505653631562628673)
                  ·
                    refine ⟨5507652379240223671971505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7343536505653631562628673 5507652379240223671971505)
                    ·
                      refine ⟨4130739284430167753978629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5507652379240223671971505 4130739284430167753978629)
                      ·
                        rfl

theorem cell23_8044586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_8044586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044586 prefixEnd_8044586 := by exact prefixLift 8044586
  have htrace : WordTrace (prefixWord ++ tailWord_8044586) baseStart_8044586 baseEnd_8044586 := by
    simpa [prefixWord, tailWord_8044586, baseEnd_8044586] using wordTrace_append hprefix tailTrace_8044586
  have hstable : (prefixWord ++ tailWord_8044586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044586).length < 2 ^ (prefixWord ++ tailWord_8044586).sum := by decide
  have hdescent : baseEnd_8044586 < baseStart_8044586 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044595 : List Nat := [1, 1, 1, 2, 4, 1, 3, 2, 3, 3, 2]
def baseStart_8044595 : Nat := 118140960795 + 8044595 * 2 ^ 59
def prefixEnd_8044595 : Nat := 4983230072969 + 3 ^ 40 * 8044595 * 2
def baseEnd_8044595 : Nat := 4130743905756058218766087

theorem tailTrace_8044595 : CollatzResearch.WordTrace tailWord_8044595 prefixEnd_8044595 4130743905756058218766087 := by
  unfold tailWord_8044595
  simp only [CollatzResearch.WordTrace]
  refine ⟨293410484290813697288751239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195606989527209131525834159 293410484290813697288751239)
  ·
    refine ⟨440115726436220545933126859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293410484290813697288751239 440115726436220545933126859)
    ·
      refine ⟨660173589654330818899690289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440115726436220545933126859 660173589654330818899690289)
      ·
        refine ⟨495130192240748114174767717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660173589654330818899690289 495130192240748114174767717)
        ·
          refine ⟨92836911045140271407768947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495130192240748114174767717 92836911045140271407768947)
          ·
            refine ⟨139255366567710407111653421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92836911045140271407768947 139255366567710407111653421)
            ·
              refine ⟨52220762462891402666870033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139255366567710407111653421 52220762462891402666870033)
              ·
                refine ⟨39165571847168552000152525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52220762462891402666870033 39165571847168552000152525)
                ·
                  refine ⟨14687089442688207000057197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39165571847168552000152525 14687089442688207000057197)
                  ·
                    refine ⟨5507658541008077625021449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14687089442688207000057197 5507658541008077625021449)
                    ·
                      refine ⟨4130743905756058218766087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5507658541008077625021449 4130743905756058218766087)
                      ·
                        rfl

theorem cell23_8044595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 3, 2].length) (baseStart_8044595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044595 prefixEnd_8044595 := by exact prefixLift 8044595
  have htrace : WordTrace (prefixWord ++ tailWord_8044595) baseStart_8044595 baseEnd_8044595 := by
    simpa [prefixWord, tailWord_8044595, baseEnd_8044595] using wordTrace_append hprefix tailTrace_8044595
  have hstable : (prefixWord ++ tailWord_8044595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044595).length < 2 ^ (prefixWord ++ tailWord_8044595).sum := by decide
  have hdescent : baseEnd_8044595 < baseStart_8044595 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044628 : List Nat := [2, 4, 1, 1, 1, 1, 1, 3, 1, 3, 5]
def baseStart_8044628 : Nat := 118140960795 + 8044628 * 2 ^ 59
def prefixEnd_8044628 : Nat := 4983230072969 + 3 ^ 40 * 8044628 * 2
def baseEnd_8044628 : Nat := 4130760850617656589653435

theorem tailTrace_8044628 : CollatzResearch.WordTrace tailWord_8044628 prefixEnd_8044628 4130760850617656589653435 := by
  unfold tailWord_8044628
  simp only [CollatzResearch.WordTrace]
  refine ⟨146705843949847071962351269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195607791933129429283135025 146705843949847071962351269)
  ·
    refine ⟨27507345740596325992940863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146705843949847071962351269 27507345740596325992940863)
    ·
      refine ⟨41261018610894488989411295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27507345740596325992940863 41261018610894488989411295)
      ·
        refine ⟨61891527916341733484116943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41261018610894488989411295 61891527916341733484116943)
        ·
          refine ⟨92837291874512600226175415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61891527916341733484116943 92837291874512600226175415)
          ·
            refine ⟨139255937811768900339263123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92837291874512600226175415 139255937811768900339263123)
            ·
              refine ⟨208883906717653350508894685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139255937811768900339263123 208883906717653350508894685)
              ·
                refine ⟨78331465019120006440835507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208883906717653350508894685 78331465019120006440835507)
                ·
                  refine ⟨117497197528680009661253261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78331465019120006440835507 117497197528680009661253261)
                  ·
                    refine ⟨44061449073255003622969973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117497197528680009661253261 44061449073255003622969973)
                    ·
                      refine ⟨4130760850617656589653435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44061449073255003622969973 4130760850617656589653435)
                      ·
                        rfl

theorem cell23_8044628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 1, 3, 5].length) (baseStart_8044628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044628 prefixEnd_8044628 := by exact prefixLift 8044628
  have htrace : WordTrace (prefixWord ++ tailWord_8044628) baseStart_8044628 baseEnd_8044628 := by
    simpa [prefixWord, tailWord_8044628, baseEnd_8044628] using wordTrace_append hprefix tailTrace_8044628
  have hstable : (prefixWord ++ tailWord_8044628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044628).length < 2 ^ (prefixWord ++ tailWord_8044628).sum := by decide
  have hdescent : baseEnd_8044628 < baseStart_8044628 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044629 : List Nat := [1, 3, 2, 2, 1, 3, 4, 1, 1, 3, 2]
def baseStart_8044629 : Nat := 118140960795 + 8044629 * 2 ^ 59
def prefixEnd_8044629 : Nat := 4983230072969 + 3 ^ 40 * 8044629 * 2
def baseEnd_8044629 : Nat := 4130761364098311085740931

theorem tailTrace_8044629 : CollatzResearch.WordTrace tailWord_8044629 prefixEnd_8044629 4130761364098311085740931 := by
  unfold tailWord_8044629
  simp only [CollatzResearch.WordTrace]
  refine ⟨293411724372690521095488941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195607816248460347396992627 293411724372690521095488941)
  ·
    refine ⟨110029396639758945410808353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293411724372690521095488941 110029396639758945410808353)
    ·
      refine ⟨82522047479819209058106265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110029396639758945410808353 82522047479819209058106265)
      ·
        refine ⟨61891535609864406793579699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82522047479819209058106265 61891535609864406793579699)
        ·
          refine ⟨92837303414796610190369549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61891535609864406793579699 92837303414796610190369549)
          ·
            refine ⟨34813988780548728821388581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92837303414796610190369549 34813988780548728821388581)
            ·
              refine ⟨6527622896352886654010359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34813988780548728821388581 6527622896352886654010359)
              ·
                refine ⟨9791434344529329981015539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6527622896352886654010359 9791434344529329981015539)
                ·
                  refine ⟨14687151516793994971523309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9791434344529329981015539 14687151516793994971523309)
                  ·
                    refine ⟨5507681818797748114321241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14687151516793994971523309 5507681818797748114321241)
                    ·
                      refine ⟨4130761364098311085740931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5507681818797748114321241 4130761364098311085740931)
                      ·
                        rfl

theorem cell23_8044629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_8044629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044629 prefixEnd_8044629 := by exact prefixLift 8044629
  have htrace : WordTrace (prefixWord ++ tailWord_8044629) baseStart_8044629 baseEnd_8044629 := by
    simpa [prefixWord, tailWord_8044629, baseEnd_8044629] using wordTrace_append hprefix tailTrace_8044629
  have hstable : (prefixWord ++ tailWord_8044629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044629).length < 2 ^ (prefixWord ++ tailWord_8044629).sum := by decide
  have hdescent : baseEnd_8044629 < baseStart_8044629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044682 : List Nat := [3, 1, 2, 3, 1, 2, 3, 3, 5]
def baseStart_8044682 : Nat := 118140960795 + 8044682 * 2 ^ 59
def prefixEnd_8044682 : Nat := 4983230072969 + 3 ^ 40 * 8044682 * 2
def baseEnd_8044682 : Nat := 458976508730333264264243

theorem tailTrace_8044682 : CollatzResearch.WordTrace tailWord_8044682 prefixEnd_8044682 458976508730333264264243 := by
  unfold tailWord_8044682
  simp only [CollatzResearch.WordTrace]
  refine ⟨73353414360374627786792075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195609104960999007431445533 73353414360374627786792075)
  ·
    refine ⟨110030121540561941680188113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73353414360374627786792075 110030121540561941680188113)
    ·
      refine ⟨82522591155421456260141085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110030121540561941680188113 82522591155421456260141085)
      ·
        refine ⟨30945971683283046097552907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82522591155421456260141085 30945971683283046097552907)
        ·
          refine ⟨46418957524924569146329361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30945971683283046097552907 46418957524924569146329361)
          ·
            refine ⟨34814218143693426859747021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46418957524924569146329361 34814218143693426859747021)
            ·
              refine ⟨13055331803885035072405133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34814218143693426859747021 13055331803885035072405133)
              ·
                refine ⟨4895749426456888152151925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13055331803885035072405133 4895749426456888152151925)
                ·
                  refine ⟨458976508730333264264243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4895749426456888152151925 458976508730333264264243)
                  ·
                    rfl

theorem cell23_8044682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 3, 3, 5].length) (baseStart_8044682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044682 prefixEnd_8044682 := by exact prefixLift 8044682
  have htrace : WordTrace (prefixWord ++ tailWord_8044682) baseStart_8044682 baseEnd_8044682 := by
    simpa [prefixWord, tailWord_8044682, baseEnd_8044682] using wordTrace_append hprefix tailTrace_8044682
  have hstable : (prefixWord ++ tailWord_8044682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044682).length < 2 ^ (prefixWord ++ tailWord_8044682).sum := by decide
  have hdescent : baseEnd_8044682 < baseStart_8044682 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044688 : List Nat := [2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 5]
def baseStart_8044688 : Nat := 118140960795 + 8044688 * 2 ^ 59
def prefixEnd_8044688 : Nat := 4983230072969 + 3 ^ 40 * 8044688 * 2
def baseEnd_8044688 : Nat := 4130791659456926354903159

theorem tailTrace_8044688 : CollatzResearch.WordTrace tailWord_8044688 prefixEnd_8044688 4130791659456926354903159 := by
  unfold tailWord_8044688
  simp only [CollatzResearch.WordTrace]
  refine ⟨146706938139738387085943359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195609250852984516114591145 146706938139738387085943359)
  ·
    refine ⟨220060407209607580628915039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146706938139738387085943359 220060407209607580628915039)
    ·
      refine ⟨330090610814411370943372559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220060407209607580628915039 330090610814411370943372559)
      ·
        refine ⟨495135916221617056415058839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330090610814411370943372559 495135916221617056415058839)
        ·
          refine ⟨742703874332425584622588259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495135916221617056415058839 742703874332425584622588259)
          ·
            refine ⟨1114055811498638376933882389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742703874332425584622588259 1114055811498638376933882389)
            ·
              refine ⟨52221366163998673918775737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1114055811498638376933882389 52221366163998673918775737)
              ·
                refine ⟨39166024622999005439081803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52221366163998673918775737 39166024622999005439081803)
                ·
                  refine ⟨58749036934498508158622705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39166024622999005439081803 58749036934498508158622705)
                  ·
                    refine ⟨44061777700873881118967029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58749036934498508158622705 44061777700873881118967029)
                    ·
                      refine ⟨4130791659456926354903159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44061777700873881118967029 4130791659456926354903159)
                      ·
                        rfl

theorem cell23_8044688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 5].length) (baseStart_8044688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044688 prefixEnd_8044688 := by exact prefixLift 8044688
  have htrace : WordTrace (prefixWord ++ tailWord_8044688) baseStart_8044688 baseEnd_8044688 := by
    simpa [prefixWord, tailWord_8044688, baseEnd_8044688] using wordTrace_append hprefix tailTrace_8044688
  have hstable : (prefixWord ++ tailWord_8044688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044688).length < 2 ^ (prefixWord ++ tailWord_8044688).sum := by decide
  have hdescent : baseEnd_8044688 < baseStart_8044688 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044705 : List Nat := [1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 5]
def baseStart_8044705 : Nat := 118140960795 + 8044705 * 2 ^ 59
def prefixEnd_8044705 : Nat := 4983230072969 + 3 ^ 40 * 8044705 * 2
def baseEnd_8044705 : Nat := 4130800388628052788390581

theorem tailTrace_8044705 : CollatzResearch.WordTrace tailWord_8044705 prefixEnd_8044705 4130800388628052788390581 := by
  unfold tailWord_8044705
  simp only [CollatzResearch.WordTrace]
  refine ⟨293414496320415186075255569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195609664213610124050170379 293414496320415186075255569)
  ·
    refine ⟨220060872240311389556441677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293414496320415186075255569 220060872240311389556441677)
    ·
      refine ⟨82522827090116771083665629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220060872240311389556441677 82522827090116771083665629)
      ·
        refine ⟨30946060158793789156374611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82522827090116771083665629 30946060158793789156374611)
        ·
          refine ⟨46419090238190683734561917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30946060158793789156374611 46419090238190683734561917)
          ·
            refine ⟨17407158839321506400460719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46419090238190683734561917 17407158839321506400460719)
            ·
              refine ⟨26110738258982259600691079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17407158839321506400460719 26110738258982259600691079)
              ·
                refine ⟨39166107388473389401036619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26110738258982259600691079 39166107388473389401036619)
                ·
                  refine ⟨58749161082710084101554929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39166107388473389401036619 58749161082710084101554929)
                  ·
                    refine ⟨44061870812032563076166197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58749161082710084101554929 44061870812032563076166197)
                    ·
                      refine ⟨4130800388628052788390581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44061870812032563076166197 4130800388628052788390581)
                      ·
                        rfl

theorem cell23_8044705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_8044705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044705 prefixEnd_8044705 := by exact prefixLift 8044705
  have htrace : WordTrace (prefixWord ++ tailWord_8044705) baseStart_8044705 baseEnd_8044705 := by
    simpa [prefixWord, tailWord_8044705, baseEnd_8044705] using wordTrace_append hprefix tailTrace_8044705
  have hstable : (prefixWord ++ tailWord_8044705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044705).length < 2 ^ (prefixWord ++ tailWord_8044705).sum := by decide
  have hdescent : baseEnd_8044705 < baseStart_8044705 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044715 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 8, 4, 2]
def baseStart_8044715 : Nat := 118140960795 + 8044715 * 2 ^ 59
def prefixEnd_8044715 : Nat := 4983230072969 + 3 ^ 40 * 8044715 * 2
def baseEnd_8044715 : Nat := 4130805523434597749265535

theorem tailTrace_8044715 : CollatzResearch.WordTrace tailWord_8044715 prefixEnd_8044715 4130805523434597749265535 := by
  unfold tailWord_8044715
  simp only [CollatzResearch.WordTrace]
  refine ⟨293414861050378957783119599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195609907366919305188746399 293414861050378957783119599)
  ·
    refine ⟨440122291575568436674679399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293414861050378957783119599 440122291575568436674679399)
    ·
      refine ⟨660183437363352655012019099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440122291575568436674679399 660183437363352655012019099)
      ·
        refine ⟨990275156045028982518028649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660183437363352655012019099 990275156045028982518028649)
        ·
          refine ⟨742706367033771736888521487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990275156045028982518028649 742706367033771736888521487)
          ·
            refine ⟨1114059550550657605332782231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742706367033771736888521487 1114059550550657605332782231)
            ·
              refine ⟨1671089325825986407999173347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114059550550657605332782231 1671089325825986407999173347)
              ·
                refine ⟨2506633988738979611998760021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1671089325825986407999173347 2506633988738979611998760021)
                ·
                  refine ⟨29374617055534917328110469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2506633988738979611998760021 29374617055534917328110469)
                  ·
                    refine ⟨5507740697912796999020713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29374617055534917328110469 5507740697912796999020713)
                    ·
                      refine ⟨4130805523434597749265535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5507740697912796999020713 4130805523434597749265535)
                      ·
                        rfl

theorem cell23_8044715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 4, 2].length) (baseStart_8044715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044715 prefixEnd_8044715 := by exact prefixLift 8044715
  have htrace : WordTrace (prefixWord ++ tailWord_8044715) baseStart_8044715 baseEnd_8044715 := by
    simpa [prefixWord, tailWord_8044715, baseEnd_8044715] using wordTrace_append hprefix tailTrace_8044715
  have hstable : (prefixWord ++ tailWord_8044715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044715).length < 2 ^ (prefixWord ++ tailWord_8044715).sum := by decide
  have hdescent : baseEnd_8044715 < baseStart_8044715 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044785 : List Nat := [1, 2, 2, 2, 2, 1, 4, 1, 3, 5]
def baseStart_8044785 : Nat := 118140960795 + 8044785 * 2 ^ 59
def prefixEnd_8044785 : Nat := 4983230072969 + 3 ^ 40 * 8044785 * 2
def baseEnd_8044785 : Nat := 1376947155693470825130071

theorem tailTrace_8044785 : CollatzResearch.WordTrace tailWord_8044785 prefixEnd_8044785 1376947155693470825130071 := by
  unfold tailWord_8044785
  simp only [CollatzResearch.WordTrace]
  refine ⟨293417414160125359738167809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195611609440083573158778539 293417414160125359738167809)
  ·
    refine ⟨220063060620094019803625857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293417414160125359738167809 220063060620094019803625857)
    ·
      refine ⟨165047295465070514852719393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220063060620094019803625857 165047295465070514852719393)
      ·
        refine ⟨123785471598802886139539545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165047295465070514852719393 123785471598802886139539545)
        ·
          refine ⟨92839103699102164604654659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123785471598802886139539545 92839103699102164604654659)
          ·
            refine ⟨139258655548653246906981989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92839103699102164604654659 139258655548653246906981989)
            ·
              refine ⟨26110997915372483795059123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139258655548653246906981989 26110997915372483795059123)
              ·
                refine ⟨39166496873058725692588685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26110997915372483795059123 39166496873058725692588685)
                ·
                  refine ⟨14687436327397022134720757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39166496873058725692588685 14687436327397022134720757)
                  ·
                    refine ⟨1376947155693470825130071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14687436327397022134720757 1376947155693470825130071)
                    ·
                      rfl

theorem cell23_8044785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 1, 3, 5].length) (baseStart_8044785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044785 prefixEnd_8044785 := by exact prefixLift 8044785
  have htrace : WordTrace (prefixWord ++ tailWord_8044785) baseStart_8044785 baseEnd_8044785 := by
    simpa [prefixWord, tailWord_8044785, baseEnd_8044785] using wordTrace_append hprefix tailTrace_8044785
  have hstable : (prefixWord ++ tailWord_8044785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044785).length < 2 ^ (prefixWord ++ tailWord_8044785).sum := by decide
  have hdescent : baseEnd_8044785 < baseStart_8044785 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044805 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 4]
def baseStart_8044805 : Nat := 118140960795 + 8044805 * 2 ^ 59
def prefixEnd_8044805 : Nat := 4983230072969 + 3 ^ 40 * 8044805 * 2
def baseEnd_8044805 : Nat := 4130851736693502397140121

theorem tailTrace_8044805 : CollatzResearch.WordTrace tailWord_8044805 prefixEnd_8044805 4130851736693502397140121 := by
  unfold tailWord_8044805
  simp only [CollatzResearch.WordTrace]
  refine ⟨293418143620052903153895869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195612095746701935435930579 293418143620052903153895869)
  ·
    refine ⟨110031803857519838682710951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293418143620052903153895869 110031803857519838682710951)
    ·
      refine ⟨165047705786279758024066427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110031803857519838682710951 165047705786279758024066427)
      ·
        refine ⟨247571558679419637036099641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165047705786279758024066427 247571558679419637036099641)
        ·
          refine ⟨185678669009564727777074731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247571558679419637036099641 185678669009564727777074731)
          ·
            refine ⟨278518003514347091665612097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185678669009564727777074731 278518003514347091665612097)
            ·
              refine ⟨208888502635760318749209073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278518003514347091665612097 208888502635760318749209073)
              ·
                refine ⟨156666376976820239061906805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208888502635760318749209073 156666376976820239061906805)
                ·
                  refine ⟨14687472841576897412053763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156666376976820239061906805 14687472841576897412053763)
                  ·
                    refine ⟨22031209262365346118080645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14687472841576897412053763 22031209262365346118080645)
                    ·
                      refine ⟨4130851736693502397140121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22031209262365346118080645 4130851736693502397140121)
                      ·
                        rfl

theorem cell23_8044805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 5, 1, 4].length) (baseStart_8044805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044805 prefixEnd_8044805 := by exact prefixLift 8044805
  have htrace : WordTrace (prefixWord ++ tailWord_8044805) baseStart_8044805 baseEnd_8044805 := by
    simpa [prefixWord, tailWord_8044805, baseEnd_8044805] using wordTrace_append hprefix tailTrace_8044805
  have hstable : (prefixWord ++ tailWord_8044805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044805).length < 2 ^ (prefixWord ++ tailWord_8044805).sum := by decide
  have hdescent : baseEnd_8044805 < baseStart_8044805 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044832 : List Nat := [2, 1, 1, 5, 2, 1, 3, 1, 1, 6]
def baseStart_8044832 : Nat := 118140960795 + 8044832 * 2 ^ 59
def prefixEnd_8044832 : Nat := 4983230072969 + 3 ^ 40 * 8044832 * 2
def baseEnd_8044832 : Nat := 1376955200223724597167499

theorem tailTrace_8044832 : CollatzResearch.WordTrace tailWord_8044832 prefixEnd_8044832 1376955200223724597167499 := by
  unfold tailWord_8044832
  simp only [CollatzResearch.WordTrace]
  refine ⟨146709564195477543382564375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195612752260636724510085833 146709564195477543382564375)
  ·
    refine ⟨220064346293216315073846563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146709564195477543382564375 220064346293216315073846563)
    ·
      refine ⟨330096519439824472610769845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220064346293216315073846563 330096519439824472610769845)
      ·
        refine ⟨30946548697483544307259673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 330096519439824472610769845 30946548697483544307259673)
        ·
          refine ⟨23209911523112658230444755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30946548697483544307259673 23209911523112658230444755)
          ·
            refine ⟨34814867284668987345667133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23209911523112658230444755 34814867284668987345667133)
            ·
              refine ⟨13055575231750870254625175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34814867284668987345667133 13055575231750870254625175)
              ·
                refine ⟨19583362847626305381937763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13055575231750870254625175 19583362847626305381937763)
                ·
                  refine ⟨29375044271439458072906645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19583362847626305381937763 29375044271439458072906645)
                  ·
                    refine ⟨1376955200223724597167499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29375044271439458072906645 1376955200223724597167499)
                    ·
                      rfl

theorem cell23_8044832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 1, 1, 6].length) (baseStart_8044832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044832 prefixEnd_8044832 := by exact prefixLift 8044832
  have htrace : WordTrace (prefixWord ++ tailWord_8044832) baseStart_8044832 baseEnd_8044832 := by
    simpa [prefixWord, tailWord_8044832, baseEnd_8044832] using wordTrace_append hprefix tailTrace_8044832
  have hstable : (prefixWord ++ tailWord_8044832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044832).length < 2 ^ (prefixWord ++ tailWord_8044832).sum := by decide
  have hdescent : baseEnd_8044832 < baseStart_8044832 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044835 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 6]
def baseStart_8044835 : Nat := 118140960795 + 8044835 * 2 ^ 59
def prefixEnd_8044835 : Nat := 4983230072969 + 3 ^ 40 * 8044835 * 2
def baseEnd_8044835 : Nat := 4130867141113137279764983

theorem tailTrace_8044835 : CollatzResearch.WordTrace tailWord_8044835 prefixEnd_8044835 4130867141113137279764983 := by
  unfold tailWord_8044835
  simp only [CollatzResearch.WordTrace]
  refine ⟨293419237809944218277487959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195612825206629478851658639 293419237809944218277487959)
  ·
    refine ⟨440128856714916327416231939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293419237809944218277487959 440128856714916327416231939)
    ·
      refine ⟨660193285072374491124347909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440128856714916327416231939 660193285072374491124347909)
      ·
        refine ⟨123786240951070217085815233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 660193285072374491124347909 123786240951070217085815233)
        ·
          refine ⟨92839680713302662814361425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123786240951070217085815233 92839680713302662814361425)
          ·
            refine ⟨69629760534976997110771069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92839680713302662814361425 69629760534976997110771069)
            ·
              refine ⟨26111160200616373916539151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69629760534976997110771069 26111160200616373916539151)
              ·
                refine ⟨39166740300924560874808727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26111160200616373916539151 39166740300924560874808727)
                ·
                  refine ⟨58750110451386841312213091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39166740300924560874808727 58750110451386841312213091)
                  ·
                    refine ⟨88125165677080261968319637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58750110451386841312213091 88125165677080261968319637)
                    ·
                      refine ⟨4130867141113137279764983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88125165677080261968319637 4130867141113137279764983)
                      ·
                        rfl

theorem cell23_8044835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_8044835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044835 prefixEnd_8044835 := by exact prefixLift 8044835
  have htrace : WordTrace (prefixWord ++ tailWord_8044835) baseStart_8044835 baseEnd_8044835 := by
    simpa [prefixWord, tailWord_8044835, baseEnd_8044835] using wordTrace_append hprefix tailTrace_8044835
  have hstable : (prefixWord ++ tailWord_8044835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044835).length < 2 ^ (prefixWord ++ tailWord_8044835).sum := by decide
  have hdescent : baseEnd_8044835 < baseStart_8044835 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044850 : List Nat := [3, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3]
def baseStart_8044850 : Nat := 118140960795 + 8044850 * 2 ^ 59
def prefixEnd_8044850 : Nat := 4983230072969 + 3 ^ 40 * 8044850 * 2
def baseEnd_8044850 : Nat := 4130874843322954721077415

theorem tailTrace_8044850 : CollatzResearch.WordTrace tailWord_8044850 prefixEnd_8044850 4130874843322954721077415 := by
  unfold tailWord_8044850
  simp only [CollatzResearch.WordTrace]
  refine ⟨73354946226222468959821001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195613189936593250559522669 73354946226222468959821001)
  ·
    refine ⟨55016209669666851719865751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73354946226222468959821001 55016209669666851719865751)
    ·
      refine ⟨82524314504500277579798627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55016209669666851719865751 82524314504500277579798627)
      ·
        refine ⟨123786471756750416369697941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82524314504500277579798627 123786471756750416369697941)
        ·
          refine ⟨5802490863597675767329591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123786471756750416369697941 5802490863597675767329591)
          ·
            refine ⟨8703736295396513650994387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5802490863597675767329591 8703736295396513650994387)
            ·
              refine ⟨13055604443094770476491581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8703736295396513650994387 13055604443094770476491581)
              ·
                refine ⟨4895851666160538928684343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13055604443094770476491581 4895851666160538928684343)
                ·
                  refine ⟨7343777499240808393026515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4895851666160538928684343 7343777499240808393026515)
                  ·
                    refine ⟨11015666248861212589539773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7343777499240808393026515 11015666248861212589539773)
                    ·
                      refine ⟨4130874843322954721077415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11015666248861212589539773 4130874843322954721077415)
                      ·
                        rfl

theorem cell23_8044850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3].length) (baseStart_8044850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044850 prefixEnd_8044850 := by exact prefixLift 8044850
  have htrace : WordTrace (prefixWord ++ tailWord_8044850) baseStart_8044850 baseEnd_8044850 := by
    simpa [prefixWord, tailWord_8044850, baseEnd_8044850] using wordTrace_append hprefix tailTrace_8044850
  have hstable : (prefixWord ++ tailWord_8044850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044850).length < 2 ^ (prefixWord ++ tailWord_8044850).sum := by decide
  have hdescent : baseEnd_8044850 < baseStart_8044850 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044862 : List Nat := [4, 2, 1, 2, 1, 4, 9]
def baseStart_8044862 : Nat := 118140960795 + 8044862 * 2 ^ 59
def prefixEnd_8044862 : Nat := 4983230072969 + 3 ^ 40 * 8044862 * 2
def baseEnd_8044862 : Nat := 50998530927047020668239

theorem tailTrace_8044862 : CollatzResearch.WordTrace tailWord_8044862 prefixEnd_8044862 50998530927047020668239 := by
  unfold tailWord_8044862
  simp only [CollatzResearch.WordTrace]
  refine ⟨36677527822605800236090105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195613481720564267925813893 36677527822605800236090105)
  ·
    refine ⟨27508145866954350177067579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36677527822605800236090105 27508145866954350177067579)
    ·
      refine ⟨41262218800431525265601369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27508145866954350177067579 41262218800431525265601369)
      ·
        refine ⟨30946664100323643949201027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41262218800431525265601369 30946664100323643949201027)
        ·
          refine ⟨46419996150485465923801541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30946664100323643949201027 46419996150485465923801541)
          ·
            refine ⟨8703749278216024860712789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 46419996150485465923801541 8703749278216024860712789)
            ·
              refine ⟨50998530927047020668239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8703749278216024860712789 50998530927047020668239)
              ·
                rfl

theorem cell23_8044862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 4, 9].length) (baseStart_8044862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044862 prefixEnd_8044862 := by exact prefixLift 8044862
  have htrace : WordTrace (prefixWord ++ tailWord_8044862) baseStart_8044862 baseEnd_8044862 := by
    simpa [prefixWord, tailWord_8044862, baseEnd_8044862] using wordTrace_append hprefix tailTrace_8044862
  have hstable : (prefixWord ++ tailWord_8044862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044862).length < 2 ^ (prefixWord ++ tailWord_8044862).sum := by decide
  have hdescent : baseEnd_8044862 < baseStart_8044862 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044899 : List Nat := [1, 1, 1, 5, 2, 1, 3, 1, 3, 3, 2]
def baseStart_8044899 : Nat := 118140960795 + 8044899 * 2 ^ 59
def prefixEnd_8044899 : Nat := 4983230072969 + 3 ^ 40 * 8044899 * 2
def baseEnd_8044899 : Nat := 4130900003875025029364689

theorem tailTrace_8044899 : CollatzResearch.WordTrace tailWord_8044899 prefixEnd_8044899 4130900003875025029364689 := by
  unfold tailWord_8044899
  simp only [CollatzResearch.WordTrace]
  refine ⟨293421572081712357207817751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195614381387808238138545167 293421572081712357207817751)
  ·
    refine ⟨440132358122568535811726627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293421572081712357207817751 440132358122568535811726627)
    ·
      refine ⟨660198537183852803717589941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440132358122568535811726627 660198537183852803717589941)
      ·
        refine ⟨61893612860986200348524057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 660198537183852803717589941 61893612860986200348524057)
        ·
          refine ⟨46420209645739650261393043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61893612860986200348524057 46420209645739650261393043)
          ·
            refine ⟨69630314468609475392089565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46420209645739650261393043 69630314468609475392089565)
            ·
              refine ⟨26111367925728553272033587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69630314468609475392089565 26111367925728553272033587)
              ·
                refine ⟨39167051888592829908050381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26111367925728553272033587 39167051888592829908050381)
                ·
                  refine ⟨14687644458222311215518893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39167051888592829908050381 14687644458222311215518893)
                  ·
                    refine ⟨5507866671833366705819585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14687644458222311215518893 5507866671833366705819585)
                    ·
                      refine ⟨4130900003875025029364689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5507866671833366705819585 4130900003875025029364689)
                      ·
                        rfl

theorem cell23_8044899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_8044899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044899 prefixEnd_8044899 := by exact prefixLift 8044899
  have htrace : WordTrace (prefixWord ++ tailWord_8044899) baseStart_8044899 baseEnd_8044899 := by
    simpa [prefixWord, tailWord_8044899, baseEnd_8044899] using wordTrace_append hprefix tailTrace_8044899
  have hstable : (prefixWord ++ tailWord_8044899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044899).length < 2 ^ (prefixWord ++ tailWord_8044899).sum := by decide
  have hdescent : baseEnd_8044899 < baseStart_8044899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044932 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_8044932 : Nat := 118140960795 + 8044932 * 2 ^ 59
def prefixEnd_8044932 : Nat := 4983230072969 + 3 ^ 40 * 8044932 * 2
def baseEnd_8044932 : Nat := 4130916948736623400252037

theorem tailTrace_8044932 : CollatzResearch.WordTrace tailWord_8044932 prefixEnd_8044932 4130916948736623400252037 := by
  unfold tailWord_8044932
  simp only [CollatzResearch.WordTrace]
  refine ⟨146711387845296401921884525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195615183793728535895846033 146711387845296401921884525)
  ·
    refine ⟨55016770441986150720706697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146711387845296401921884525 55016770441986150720706697)
    ·
      refine ⟨41262577831489613040530023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55016770441986150720706697 41262577831489613040530023)
      ·
        refine ⟨61893866747234419560795035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41262577831489613040530023 61893866747234419560795035)
        ·
          refine ⟨92840800120851629341192553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61893866747234419560795035 92840800120851629341192553)
          ·
            refine ⟨69630600090638722005894415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92840800120851629341192553 69630600090638722005894415)
            ·
              refine ⟨104445900135958083008841623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69630600090638722005894415 104445900135958083008841623)
              ·
                refine ⟨156668850203937124513262435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104445900135958083008841623 156668850203937124513262435)
                ·
                  refine ⟨235003275305905686769893653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156668850203937124513262435 235003275305905686769893653)
                  ·
                    refine ⟨11015778529964329067338765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 235003275305905686769893653 11015778529964329067338765)
                    ·
                      refine ⟨4130916948736623400252037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11015778529964329067338765 4130916948736623400252037)
                      ·
                        rfl

theorem cell23_8044932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_8044932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044932 prefixEnd_8044932 := by exact prefixLift 8044932
  have htrace : WordTrace (prefixWord ++ tailWord_8044932) baseStart_8044932 baseEnd_8044932 := by
    simpa [prefixWord, tailWord_8044932, baseEnd_8044932] using wordTrace_append hprefix tailTrace_8044932
  have hstable : (prefixWord ++ tailWord_8044932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044932).length < 2 ^ (prefixWord ++ tailWord_8044932).sum := by decide
  have hdescent : baseEnd_8044932 < baseStart_8044932 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8044952 : List Nat := [2, 1, 2, 5, 1, 1, 1, 1, 9]
def baseStart_8044952 : Nat := 118140960795 + 8044952 * 2 ^ 59
def prefixEnd_8044952 : Nat := 4983230072969 + 3 ^ 40 * 8044952 * 2
def baseEnd_8044952 : Nat := 458991913149968146889105

theorem tailTrace_8044952 : CollatzResearch.WordTrace tailWord_8044952 prefixEnd_8044952 458991913149968146889105 := by
  unfold tailWord_8044952
  simp only [CollatzResearch.WordTrace]
  refine ⟨146711752575260173629748555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195615670100346898172998073 146711752575260173629748555)
  ·
    refine ⟨220067628862890260444622833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146711752575260173629748555 220067628862890260444622833)
    ·
      refine ⟨165050721647167695333467125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220067628862890260444622833 165050721647167695333467125)
      ·
        refine ⟨15473505154421971437512543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 165050721647167695333467125 15473505154421971437512543)
        ·
          refine ⟨23210257731632957156268815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15473505154421971437512543 23210257731632957156268815)
          ·
            refine ⟨34815386597449435734403223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23210257731632957156268815 34815386597449435734403223)
            ·
              refine ⟨52223079896174153601604835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34815386597449435734403223 52223079896174153601604835)
              ·
                refine ⟨78334619844261230402407253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52223079896174153601604835 78334619844261230402407253)
                ·
                  refine ⟨458991913149968146889105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 78334619844261230402407253 458991913149968146889105)
                  ·
                    rfl

theorem cell23_8044952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 1, 9].length) (baseStart_8044952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8044952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8044952 prefixEnd_8044952 := by exact prefixLift 8044952
  have htrace : WordTrace (prefixWord ++ tailWord_8044952) baseStart_8044952 baseEnd_8044952 := by
    simpa [prefixWord, tailWord_8044952, baseEnd_8044952] using wordTrace_append hprefix tailTrace_8044952
  have hstable : (prefixWord ++ tailWord_8044952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8044952).length < 2 ^ (prefixWord ++ tailWord_8044952).sum := by decide
  have hdescent : baseEnd_8044952 < baseStart_8044952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8044952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045002 : List Nat := [3, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4]
def baseStart_8045002 : Nat := 118140960795 + 8045002 * 2 ^ 59
def prefixEnd_8045002 : Nat := 4983230072969 + 3 ^ 40 * 8045002 * 2
def baseEnd_8045002 : Nat := 4130952892382438126376715

theorem tailTrace_8045002 : CollatzResearch.WordTrace tailWord_8045002 prefixEnd_8045002 4130952892382438126376715 := by
  unfold tailWord_8045002
  simp only [CollatzResearch.WordTrace]
  refine ⟨73356332200084801449704315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195616885866892803865878173 73356332200084801449704315)
  ·
    refine ⟨110034498300127202174556473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73356332200084801449704315 110034498300127202174556473)
    ·
      refine ⟨82525873725095401630917355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110034498300127202174556473 82525873725095401630917355)
      ·
        refine ⟨123788810587643102446376033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82525873725095401630917355 123788810587643102446376033)
        ·
          refine ⟨92841607940732326834782025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123788810587643102446376033 92841607940732326834782025)
          ·
            refine ⟨69631205955549245126086519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92841607940732326834782025 69631205955549245126086519)
            ·
              refine ⟨104446808933323867689129779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69631205955549245126086519 104446808933323867689129779)
              ·
                refine ⟨156670213399985801533694669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104446808933323867689129779 156670213399985801533694669)
                ·
                  refine ⟨58751330024994675575135501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156670213399985801533694669 58751330024994675575135501)
                  ·
                    refine ⟨22031748759373003340675813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58751330024994675575135501 22031748759373003340675813)
                    ·
                      refine ⟨4130952892382438126376715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22031748759373003340675813 4130952892382438126376715)
                      ·
                        rfl

theorem cell23_8045002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 1, 3, 3, 4].length) (baseStart_8045002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045002 prefixEnd_8045002 := by exact prefixLift 8045002
  have htrace : WordTrace (prefixWord ++ tailWord_8045002) baseStart_8045002 baseEnd_8045002 := by
    simpa [prefixWord, tailWord_8045002, baseEnd_8045002] using wordTrace_append hprefix tailTrace_8045002
  have hstable : (prefixWord ++ tailWord_8045002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045002).length < 2 ^ (prefixWord ++ tailWord_8045002).sum := by decide
  have hdescent : baseEnd_8045002 < baseStart_8045002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045109 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 4]
def baseStart_8045109 : Nat := 118140960795 + 8045109 * 2 ^ 59
def prefixEnd_8045109 : Nat := 4983230072969 + 3 ^ 40 * 8045109 * 2
def baseEnd_8045109 : Nat := 4131007834812469207738723

theorem tailTrace_8045109 : CollatzResearch.WordTrace tailWord_8045109 prefixEnd_8045109 4131007834812469207738723 := by
  unfold tailWord_8045109
  simp only [CollatzResearch.WordTrace]
  refine ⟨293429231410951563072962381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195619487607301042048641587 293429231410951563072962381)
  ·
    refine ⟨110035961779106836152360893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293429231410951563072962381 110035961779106836152360893)
    ·
      refine ⟨41263485667165063557135335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110035961779106836152360893 41263485667165063557135335)
      ·
        refine ⟨61895228500747595335703003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41263485667165063557135335 61895228500747595335703003)
        ·
          refine ⟨92842842751121393003554505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61895228500747595335703003 92842842751121393003554505)
          ·
            refine ⟨69632132063341044752665879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92842842751121393003554505 69632132063341044752665879)
            ·
              refine ⟨104448198095011567128998819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69632132063341044752665879 104448198095011567128998819)
              ·
                refine ⟨156672297142517350693498229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104448198095011567128998819 156672297142517350693498229)
                ·
                  refine ⟨14688027857111001627515459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 156672297142517350693498229 14688027857111001627515459)
                  ·
                    refine ⟨22032041785666502441273189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14688027857111001627515459 22032041785666502441273189)
                    ·
                      refine ⟨4131007834812469207738723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22032041785666502441273189 4131007834812469207738723)
                      ·
                        rfl

theorem cell23_8045109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_8045109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045109 prefixEnd_8045109 := by exact prefixLift 8045109
  have htrace : WordTrace (prefixWord ++ tailWord_8045109) baseStart_8045109 baseEnd_8045109 := by
    simpa [prefixWord, tailWord_8045109, baseEnd_8045109] using wordTrace_append hprefix tailTrace_8045109
  have hstable : (prefixWord ++ tailWord_8045109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045109).length < 2 ^ (prefixWord ++ tailWord_8045109).sum := by decide
  have hdescent : baseEnd_8045109 < baseStart_8045109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045119 : List Nat := [1, 1, 2, 2, 3, 2, 4, 1, 1, 6]
def baseStart_8045119 : Nat := 118140960795 + 8045119 * 2 ^ 59
def prefixEnd_8045119 : Nat := 4983230072969 + 3 ^ 40 * 8045119 * 2
def baseEnd_8045119 : Nat := 1377004323206338056204559

theorem tailTrace_8045119 : CollatzResearch.WordTrace tailWord_8045119 prefixEnd_8045119 1377004323206338056204559 := by
  unfold tailWord_8045119
  simp only [CollatzResearch.WordTrace]
  refine ⟨293429596140915334780826411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195619730760610223187217607 293429596140915334780826411)
  ·
    refine ⟨440144394211373002171239617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293429596140915334780826411 440144394211373002171239617)
    ·
      refine ⟨330108295658529751628429713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440144394211373002171239617 330108295658529751628429713)
      ·
        refine ⟨247581221743897313721322285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330108295658529751628429713 247581221743897313721322285)
        ·
          refine ⟨92842958153961492645495857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247581221743897313721322285 92842958153961492645495857)
          ·
            refine ⟨69632218615471119484121893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92842958153961492645495857 69632218615471119484121893)
            ·
              refine ⟨13056040990400834903272855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69632218615471119484121893 13056040990400834903272855)
              ·
                refine ⟨19584061485601252354909283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13056040990400834903272855 19584061485601252354909283)
                ·
                  refine ⟨29376092228401878532363925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19584061485601252354909283 29376092228401878532363925)
                  ·
                    refine ⟨1377004323206338056204559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29376092228401878532363925 1377004323206338056204559)
                    ·
                      rfl

theorem cell23_8045119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 1, 1, 6].length) (baseStart_8045119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045119 prefixEnd_8045119 := by exact prefixLift 8045119
  have htrace : WordTrace (prefixWord ++ tailWord_8045119) baseStart_8045119 baseEnd_8045119 := by
    simpa [prefixWord, tailWord_8045119, baseEnd_8045119] using wordTrace_append hprefix tailTrace_8045119
  have hstable : (prefixWord ++ tailWord_8045119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045119).length < 2 ^ (prefixWord ++ tailWord_8045119).sum := by decide
  have hdescent : baseEnd_8045119 < baseStart_8045119 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045124 : List Nat := [2, 3, 5, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_8045124 : Nat := 118140960795 + 8045124 * 2 ^ 59
def prefixEnd_8045124 : Nat := 4983230072969 + 3 ^ 40 * 8045124 * 2
def baseEnd_8045124 : Nat := 4131015537022286649051155

theorem tailTrace_8045124 : CollatzResearch.WordTrace tailWord_8045124 prefixEnd_8045124 4131015537022286649051155 := by
  unfold tailWord_8045124
  simp only [CollatzResearch.WordTrace]
  refine ⟨146714889252948610317379213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195619852337264813756505617 146714889252948610317379213)
  ·
    refine ⟨55018083469855728869017205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146714889252948610317379213 55018083469855728869017205)
    ·
      refine ⟨5157945325298974581470363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 55018083469855728869017205 5157945325298974581470363)
      ·
        refine ⟨7736917987948461872205545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5157945325298974581470363 7736917987948461872205545)
        ·
          refine ⟨5802688490961346404154159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7736917987948461872205545 5802688490961346404154159)
          ·
            refine ⟨8704032736442019606231239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5802688490961346404154159 8704032736442019606231239)
            ·
              refine ⟨13056049104663029409346859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8704032736442019606231239 13056049104663029409346859)
              ·
                refine ⟨19584073656994544114020289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13056049104663029409346859 19584073656994544114020289)
                ·
                  refine ⟨14688055242745908085515217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19584073656994544114020289 14688055242745908085515217)
                  ·
                    refine ⟨11016041432059431064136413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14688055242745908085515217 11016041432059431064136413)
                    ·
                      refine ⟨4131015537022286649051155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11016041432059431064136413 4131015537022286649051155)
                      ·
                        rfl

theorem cell23_8045124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_8045124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045124 prefixEnd_8045124 := by exact prefixLift 8045124
  have htrace : WordTrace (prefixWord ++ tailWord_8045124) baseStart_8045124 baseEnd_8045124 := by
    simpa [prefixWord, tailWord_8045124, baseEnd_8045124] using wordTrace_append hprefix tailTrace_8045124
  have hstable : (prefixWord ++ tailWord_8045124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045124).length < 2 ^ (prefixWord ++ tailWord_8045124).sum := by decide
  have hdescent : baseEnd_8045124 < baseStart_8045124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045153 : List Nat := [1, 2, 3, 1, 1, 6, 1, 2, 2, 4]
def baseStart_8045153 : Nat := 118140960795 + 8045153 * 2 ^ 59
def prefixEnd_8045153 : Nat := 4983230072969 + 3 ^ 40 * 8045153 * 2
def baseEnd_8045153 : Nat := 1377010142653755678529507

theorem tailTrace_8045153 : CollatzResearch.WordTrace tailWord_8045153 prefixEnd_8045153 1377010142653755678529507 := by
  unfold tailWord_8045153
  simp only [CollatzResearch.WordTrace]
  refine ⟨293430836222792158587564113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195620557481861439058376075 293430836222792158587564113)
  ·
    refine ⟨220073127167094118940673085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293430836222792158587564113 220073127167094118940673085)
    ·
      refine ⟨82527422687660294602752407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220073127167094118940673085 82527422687660294602752407)
      ·
        refine ⟨123791134031490441904128611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82527422687660294602752407 123791134031490441904128611)
        ·
          refine ⟨185686701047235662856192917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123791134031490441904128611 185686701047235662856192917)
          ·
            refine ⟨8704064111589171696384043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 185686701047235662856192917 8704064111589171696384043)
            ·
              refine ⟨13056096167383757544576065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8704064111589171696384043 13056096167383757544576065)
              ·
                refine ⟨9792072125537818158432049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13056096167383757544576065 9792072125537818158432049)
                ·
                  refine ⟨7344054094153363618824037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9792072125537818158432049 7344054094153363618824037)
                  ·
                    refine ⟨1377010142653755678529507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7344054094153363618824037 1377010142653755678529507)
                    ·
                      rfl

theorem cell23_8045153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 2, 2, 4].length) (baseStart_8045153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045153 prefixEnd_8045153 := by exact prefixLift 8045153
  have htrace : WordTrace (prefixWord ++ tailWord_8045153) baseStart_8045153 baseEnd_8045153 := by
    simpa [prefixWord, tailWord_8045153, baseEnd_8045153] using wordTrace_append hprefix tailTrace_8045153
  have hstable : (prefixWord ++ tailWord_8045153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045153).length < 2 ^ (prefixWord ++ tailWord_8045153).sum := by decide
  have hdescent : baseEnd_8045153 < baseStart_8045153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045170 : List Nat := [3, 2, 1, 2, 4, 1, 3, 1, 2, 4]
def baseStart_8045170 : Nat := 118140960795 + 8045170 * 2 ^ 59
def prefixEnd_8045170 : Nat := 4983230072969 + 3 ^ 40 * 8045170 * 2
def baseEnd_8045170 : Nat := 1377013052377464489691981

theorem tailTrace_8045170 : CollatzResearch.WordTrace tailWord_8045170 prefixEnd_8045170 1377013052377464489691981 := by
  unfold tailWord_8045170
  simp only [CollatzResearch.WordTrace]
  refine ⟨73357864065932642622733241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195620970842487046993955309 73357864065932642622733241)
  ·
    refine ⟨55018398049449481967049931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73357864065932642622733241 55018398049449481967049931)
    ·
      refine ⟨82527597074174222950574897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55018398049449481967049931 82527597074174222950574897)
      ·
        refine ⟨61895697805630667212931173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82527597074174222950574897 61895697805630667212931173)
        ·
          refine ⟨11605443338555750102424595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61895697805630667212931173 11605443338555750102424595)
          ·
            refine ⟨17408165007833625153636893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11605443338555750102424595 17408165007833625153636893)
            ·
              refine ⟨6528061877937609432613835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17408165007833625153636893 6528061877937609432613835)
              ·
                refine ⟨9792092816906414148920753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6528061877937609432613835 9792092816906414148920753)
                ·
                  refine ⟨7344069612679810611690565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9792092816906414148920753 7344069612679810611690565)
                  ·
                    refine ⟨1377013052377464489691981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7344069612679810611690565 1377013052377464489691981)
                    ·
                      rfl

theorem cell23_8045170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 3, 1, 2, 4].length) (baseStart_8045170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045170 prefixEnd_8045170 := by exact prefixLift 8045170
  have htrace : WordTrace (prefixWord ++ tailWord_8045170) baseStart_8045170 baseEnd_8045170 := by
    simpa [prefixWord, tailWord_8045170, baseEnd_8045170] using wordTrace_append hprefix tailTrace_8045170
  have hstable : (prefixWord ++ tailWord_8045170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045170).length < 2 ^ (prefixWord ++ tailWord_8045170).sum := by decide
  have hdescent : baseEnd_8045170 < baseStart_8045170 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045189 : List Nat := [1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 5]
def baseStart_8045189 : Nat := 118140960795 + 8045189 * 2 ^ 59
def prefixEnd_8045189 : Nat := 4983230072969 + 3 ^ 40 * 8045189 * 2
def baseEnd_8045189 : Nat := 4131048913264828894738355

theorem tailTrace_8045189 : CollatzResearch.WordTrace tailWord_8045189 prefixEnd_8045189 4131048913264828894738355 := by
  unfold tailWord_8045189
  simp only [CollatzResearch.WordTrace]
  refine ⟨293432149250661736735874621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195621432833774491157249747 293432149250661736735874621)
  ·
    refine ⟨110037055968998151275952983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293432149250661736735874621 110037055968998151275952983)
    ·
      refine ⟨165055583953497226913929475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110037055968998151275952983 165055583953497226913929475)
      ·
        refine ⟨247583375930245840370894213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165055583953497226913929475 247583375930245840370894213)
        ·
          refine ⟨46421882986921095069542665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247583375930245840370894213 46421882986921095069542665)
          ·
            refine ⟨34816412240190821302156999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46421882986921095069542665 34816412240190821302156999)
            ·
              refine ⟨52224618360286231953235499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34816412240190821302156999 52224618360286231953235499)
              ·
                refine ⟨78336927540429347929853249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52224618360286231953235499 78336927540429347929853249)
                ·
                  refine ⟨58752695655322010947389937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78336927540429347929853249 58752695655322010947389937)
                  ·
                    refine ⟨44064521741491508210542453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58752695655322010947389937 44064521741491508210542453)
                    ·
                      refine ⟨4131048913264828894738355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44064521741491508210542453 4131048913264828894738355)
                      ·
                        rfl

theorem cell23_8045189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 2, 2, 5].length) (baseStart_8045189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045189 prefixEnd_8045189 := by exact prefixLift 8045189
  have htrace : WordTrace (prefixWord ++ tailWord_8045189) baseStart_8045189 baseEnd_8045189 := by
    simpa [prefixWord, tailWord_8045189, baseEnd_8045189] using wordTrace_append hprefix tailTrace_8045189
  have hstable : (prefixWord ++ tailWord_8045189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045189).length < 2 ^ (prefixWord ++ tailWord_8045189).sum := by decide
  have hdescent : baseEnd_8045189 < baseStart_8045189 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045194 : List Nat := [3, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2]
def baseStart_8045194 : Nat := 118140960795 + 8045194 * 2 ^ 59
def prefixEnd_8045194 : Nat := 4983230072969 + 3 ^ 40 * 8045194 * 2
def baseEnd_8045194 : Nat := 4131051480668101375175833

theorem tailTrace_8045194 : CollatzResearch.WordTrace tailWord_8045194 prefixEnd_8045194 4131051480668101375175833 := by
  unfold tailWord_8045194
  simp only [CollatzResearch.WordTrace]
  refine ⟨73358082903910905647451659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195621554410429081726537757 73358082903910905647451659)
  ·
    refine ⟨110037124355866358471177489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73358082903910905647451659 110037124355866358471177489)
    ·
      refine ⟨82527843266899768853383117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110037124355866358471177489 82527843266899768853383117)
      ·
        refine ⟨30947941225087413320018669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82527843266899768853383117 30947941225087413320018669)
        ·
          refine ⟨11605477959407779995007001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30947941225087413320018669 11605477959407779995007001)
          ·
            refine ⟨8704108469555834996255251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11605477959407779995007001 8704108469555834996255251)
            ·
              refine ⟨13056162704333752494382877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8704108469555834996255251 13056162704333752494382877)
              ·
                refine ⟨4896061014125157185393579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13056162704333752494382877 4896061014125157185393579)
                ·
                  refine ⟨7344091521187735778090369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896061014125157185393579 7344091521187735778090369)
                  ·
                    refine ⟨5508068640890801833567777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7344091521187735778090369 5508068640890801833567777)
                    ·
                      refine ⟨4131051480668101375175833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508068640890801833567777 4131051480668101375175833)
                      ·
                        rfl

theorem cell23_8045194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 1, 3, 1, 2, 2].length) (baseStart_8045194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045194 prefixEnd_8045194 := by exact prefixLift 8045194
  have htrace : WordTrace (prefixWord ++ tailWord_8045194) baseStart_8045194 baseEnd_8045194 := by
    simpa [prefixWord, tailWord_8045194, baseEnd_8045194] using wordTrace_append hprefix tailTrace_8045194
  have hstable : (prefixWord ++ tailWord_8045194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045194).length < 2 ^ (prefixWord ++ tailWord_8045194).sum := by decide
  have hdescent : baseEnd_8045194 < baseStart_8045194 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045237 : List Nat := [1, 3, 3, 3, 1, 3, 1, 2, 1, 3, 2]
def baseStart_8045237 : Nat := 118140960795 + 8045237 * 2 ^ 59
def prefixEnd_8045237 : Nat := 4983230072969 + 3 ^ 40 * 8045237 * 2
def baseEnd_8045237 : Nat := 4131073560336244706938135

theorem tailTrace_8045237 : CollatzResearch.WordTrace tailWord_8045237 prefixEnd_8045237 4131073560336244706938135 := by
  unfold tailWord_8045237
  simp only [CollatzResearch.WordTrace]
  refine ⟨293433899954487840933621965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195622599969658560622414643 293433899954487840933621965)
  ·
    refine ⟨110037712482932940350108237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293433899954487840933621965 110037712482932940350108237)
    ·
      refine ⟨41264142181099852631290589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110037712482932940350108237 41264142181099852631290589)
      ·
        refine ⟨15474053317912444736733971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41264142181099852631290589 15474053317912444736733971)
        ·
          refine ⟨23211079976868667105100957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15474053317912444736733971 23211079976868667105100957)
          ·
            refine ⟨8704154991325750164412859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23211079976868667105100957 8704154991325750164412859)
            ·
              refine ⟨13056232486988625246619289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8704154991325750164412859 13056232486988625246619289)
              ·
                refine ⟨9792174365241468934964467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13056232486988625246619289 9792174365241468934964467)
                ·
                  refine ⟨14688261547862203402446701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9792174365241468934964467 14688261547862203402446701)
                  ·
                    refine ⟨5508098080448326275917513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14688261547862203402446701 5508098080448326275917513)
                    ·
                      refine ⟨4131073560336244706938135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508098080448326275917513 4131073560336244706938135)
                      ·
                        rfl

theorem cell23_8045237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_8045237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045237 prefixEnd_8045237 := by exact prefixLift 8045237
  have htrace : WordTrace (prefixWord ++ tailWord_8045237) baseStart_8045237 baseEnd_8045237 := by
    simpa [prefixWord, tailWord_8045237, baseEnd_8045237] using wordTrace_append hprefix tailTrace_8045237
  have hstable : (prefixWord ++ tailWord_8045237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045237).length < 2 ^ (prefixWord ++ tailWord_8045237).sum := by decide
  have hdescent : baseEnd_8045237 < baseStart_8045237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045283 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 3]
def baseStart_8045283 : Nat := 118140960795 + 8045283 * 2 ^ 59
def prefixEnd_8045283 : Nat := 4983230072969 + 3 ^ 40 * 8045283 * 2
def baseEnd_8045283 : Nat := 4131097180446351526962923

theorem tailTrace_8045283 : CollatzResearch.WordTrace tailWord_8045283 prefixEnd_8045283 4131097180446351526962923 := by
  unfold tailWord_8045283
  simp only [CollatzResearch.WordTrace]
  refine ⟨293435577712321190789796503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195623718474880793859864335 293435577712321190789796503)
  ·
    refine ⟨440153366568481786184694755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293435577712321190789796503 440153366568481786184694755)
    ·
      refine ⟨660230049852722679277042133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440153366568481786184694755 660230049852722679277042133)
      ·
        refine ⟨15474141793423187795555675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 660230049852722679277042133 15474141793423187795555675)
        ·
          refine ⟨23211212690134781693333513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15474141793423187795555675 23211212690134781693333513)
          ·
            refine ⟨17408409517601086270000135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23211212690134781693333513 17408409517601086270000135)
            ·
              refine ⟨26112614276401629405000203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17408409517601086270000135 26112614276401629405000203)
              ·
                refine ⟨39168921414602444107500305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26112614276401629405000203 39168921414602444107500305)
                ·
                  refine ⟨29376691060951833080625229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39168921414602444107500305 29376691060951833080625229)
                  ·
                    refine ⟨11016259147856937405234461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29376691060951833080625229 11016259147856937405234461)
                    ·
                      refine ⟨4131097180446351526962923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11016259147856937405234461 4131097180446351526962923)
                      ·
                        rfl

theorem cell23_8045283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_8045283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045283 prefixEnd_8045283 := by exact prefixLift 8045283
  have htrace : WordTrace (prefixWord ++ tailWord_8045283) baseStart_8045283 baseEnd_8045283 := by
    simpa [prefixWord, tailWord_8045283, baseEnd_8045283] using wordTrace_append hprefix tailTrace_8045283
  have hstable : (prefixWord ++ tailWord_8045283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045283).length < 2 ^ (prefixWord ++ tailWord_8045283).sum := by decide
  have hdescent : baseEnd_8045283 < baseStart_8045283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045293 : List Nat := [1, 5, 1, 2, 1, 1, 1, 2, 2, 5, 2]
def baseStart_8045293 : Nat := 118140960795 + 8045293 * 2 ^ 59
def prefixEnd_8045293 : Nat := 4983230072969 + 3 ^ 40 * 8045293 * 2
def baseEnd_8045293 : Nat := 4131102315252896487837877

theorem tailTrace_8045293 : CollatzResearch.WordTrace tailWord_8045293 prefixEnd_8045293 4131102315252896487837877 := by
  unfold tailWord_8045293
  simp only [CollatzResearch.WordTrace]
  refine ⟨293435942442284962497660533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195623961628189974998440355 293435942442284962497660533)
  ·
    refine ⟨27509619603964215234155675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293435942442284962497660533 27509619603964215234155675)
    ·
      refine ⟨41264429405946322851233513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27509619603964215234155675 41264429405946322851233513)
      ·
        refine ⟨30948322054459742138425135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41264429405946322851233513 30948322054459742138425135)
        ·
          refine ⟨46422483081689613207637703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30948322054459742138425135 46422483081689613207637703)
          ·
            refine ⟨69633724622534419811456555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46422483081689613207637703 69633724622534419811456555)
            ·
              refine ⟨104450586933801629717184833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69633724622534419811456555 104450586933801629717184833)
              ·
                refine ⟨78337940200351222287888625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104450586933801629717184833 78337940200351222287888625)
                ·
                  refine ⟨58753455150263416715916469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78337940200351222287888625 58753455150263416715916469)
                  ·
                    refine ⟨5508136420337195317117169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58753455150263416715916469 5508136420337195317117169)
                    ·
                      refine ⟨4131102315252896487837877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508136420337195317117169 4131102315252896487837877)
                      ·
                        rfl

theorem cell23_8045293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_8045293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045293 prefixEnd_8045293 := by exact prefixLift 8045293
  have htrace : WordTrace (prefixWord ++ tailWord_8045293) baseStart_8045293 baseEnd_8045293 := by
    simpa [prefixWord, tailWord_8045293, baseEnd_8045293] using wordTrace_append hprefix tailTrace_8045293
  have hstable : (prefixWord ++ tailWord_8045293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045293).length < 2 ^ (prefixWord ++ tailWord_8045293).sum := by decide
  have hdescent : baseEnd_8045293 < baseStart_8045293 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045333 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 3, 4]
def baseStart_8045333 : Nat := 118140960795 + 8045333 * 2 ^ 59
def prefixEnd_8045333 : Nat := 4983230072969 + 3 ^ 40 * 8045333 * 2
def baseEnd_8045333 : Nat := 1377040951493025443779231

theorem tailTrace_8045333 : CollatzResearch.WordTrace tailWord_8045333 prefixEnd_8045333 1377040951493025443779231 := by
  unfold tailWord_8045333
  simp only [CollatzResearch.WordTrace]
  refine ⟨293437401362140049329116653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195624934241426699552744435 293437401362140049329116653)
  ·
    refine ⟨110039025510802518498418745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293437401362140049329116653 110039025510802518498418745)
    ·
      refine ⟨82529269133101888873814059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110039025510802518498418745 82529269133101888873814059)
      ·
        refine ⟨123793903699652833310721089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82529269133101888873814059 123793903699652833310721089)
        ·
          refine ⟨92845427774739624983040817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123793903699652833310721089 92845427774739624983040817)
          ·
            refine ⟨69634070831054718737280613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92845427774739624983040817 69634070831054718737280613)
            ·
              refine ⟨13056388280822759763240115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69634070831054718737280613 13056388280822759763240115)
              ·
                refine ⟨19584582421234139644860173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13056388280822759763240115 19584582421234139644860173)
                ·
                  refine ⟨7344218407962802366822565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19584582421234139644860173 7344218407962802366822565)
                  ·
                    refine ⟨1377040951493025443779231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7344218407962802366822565 1377040951493025443779231)
                    ·
                      rfl

theorem cell23_8045333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_8045333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045333 prefixEnd_8045333 := by exact prefixLift 8045333
  have htrace : WordTrace (prefixWord ++ tailWord_8045333) baseStart_8045333 baseEnd_8045333 := by
    simpa [prefixWord, tailWord_8045333, baseEnd_8045333] using wordTrace_append hprefix tailTrace_8045333
  have hstable : (prefixWord ++ tailWord_8045333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045333).length < 2 ^ (prefixWord ++ tailWord_8045333).sum := by decide
  have hdescent : baseEnd_8045333 < baseStart_8045333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045356 : List Nat := [2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 3]
def baseStart_8045356 : Nat := 118140960795 + 8045356 * 2 ^ 59
def prefixEnd_8045356 : Nat := 4983230072969 + 3 ^ 40 * 8045356 * 2
def baseEnd_8045356 : Nat := 4131134664534129741350087

theorem tailTrace_8045356 : CollatzResearch.WordTrace tailWord_8045356 prefixEnd_8045356 4131134664534129741350087 := by
  unfold tailWord_8045356
  simp only [CollatzResearch.WordTrace]
  refine ⟨146719120120528362128601961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195625493494037816171469281 146719120120528362128601961)
  ·
    refine ⟨110039340090396271596451471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146719120120528362128601961 110039340090396271596451471)
    ·
      refine ⟨165059010135594407394677207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110039340090396271596451471 165059010135594407394677207)
      ·
        refine ⟨247588515203391611092015811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165059010135594407394677207 247588515203391611092015811)
        ·
          refine ⟨371382772805087416638023717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247588515203391611092015811 371382772805087416638023717)
          ·
            refine ⟨69634269900953890619629447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 371382772805087416638023717 69634269900953890619629447)
            ·
              refine ⟨104451404851430835929444171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69634269900953890619629447 104451404851430835929444171)
              ·
                refine ⟨156677107277146253894166257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104451404851430835929444171 156677107277146253894166257)
                ·
                  refine ⟨117507830457859690420624693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156677107277146253894166257 117507830457859690420624693)
                  ·
                    refine ⟨11016359105424345976933565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117507830457859690420624693 11016359105424345976933565)
                    ·
                      refine ⟨4131134664534129741350087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11016359105424345976933565 4131134664534129741350087)
                      ·
                        rfl

theorem cell23_8045356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_8045356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045356 prefixEnd_8045356 := by exact prefixLift 8045356
  have htrace : WordTrace (prefixWord ++ tailWord_8045356) baseStart_8045356 baseEnd_8045356 := by
    simpa [prefixWord, tailWord_8045356, baseEnd_8045356] using wordTrace_append hprefix tailTrace_8045356
  have hstable : (prefixWord ++ tailWord_8045356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045356).length < 2 ^ (prefixWord ++ tailWord_8045356).sum := by decide
  have hdescent : baseEnd_8045356 < baseStart_8045356 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045377 : List Nat := [1, 2, 5, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_8045377 : Nat := 118140960795 + 8045377 * 2 ^ 59
def prefixEnd_8045377 : Nat := 4983230072969 + 3 ^ 40 * 8045377 * 2
def baseEnd_8045377 : Nat := 4131145447627874159187491

theorem tailTrace_8045377 : CollatzResearch.WordTrace tailWord_8045377 prefixEnd_8045377 4131145447627874159187491 := by
  unfold tailWord_8045377
  simp only [CollatzResearch.WordTrace]
  refine ⟨293439006173980644843718385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195626004115987096562478923 293439006173980644843718385)
  ·
    refine ⟨220079254630485483632788789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293439006173980644843718385 220079254630485483632788789)
    ·
      refine ⟨20632430121608014090573949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220079254630485483632788789 20632430121608014090573949)
      ·
        refine ⟨7737161295603005283965231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20632430121608014090573949 7737161295603005283965231)
        ·
          refine ⟨11605741943404507925947847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7737161295603005283965231 11605741943404507925947847)
          ·
            refine ⟨17408612915106761888921771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11605741943404507925947847 17408612915106761888921771)
            ·
              refine ⟨26112919372660142833382657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17408612915106761888921771 26112919372660142833382657)
              ·
                refine ⟨19584689529495107125036993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26112919372660142833382657 19584689529495107125036993)
                ·
                  refine ⟨14688517147121330343777745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19584689529495107125036993 14688517147121330343777745)
                  ·
                    refine ⟨11016387860340997757833309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14688517147121330343777745 11016387860340997757833309)
                    ·
                      refine ⟨4131145447627874159187491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11016387860340997757833309 4131145447627874159187491)
                      ·
                        rfl

theorem cell23_8045377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_8045377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045377 prefixEnd_8045377 := by exact prefixLift 8045377
  have htrace : WordTrace (prefixWord ++ tailWord_8045377) baseStart_8045377 baseEnd_8045377 := by
    simpa [prefixWord, tailWord_8045377, baseEnd_8045377] using wordTrace_append hprefix tailTrace_8045377
  have hstable : (prefixWord ++ tailWord_8045377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045377).length < 2 ^ (prefixWord ++ tailWord_8045377).sum := by decide
  have hdescent : baseEnd_8045377 < baseStart_8045377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045410 : List Nat := [3, 3, 2, 1, 3, 1, 1, 1, 3, 5]
def baseStart_8045410 : Nat := 118140960795 + 8045410 * 2 ^ 59
def prefixEnd_8045410 : Nat := 4983230072969 + 3 ^ 40 * 8045410 * 2
def baseEnd_8045410 : Nat := 1377054130829824176691613

theorem tailTrace_8045410 : CollatzResearch.WordTrace tailWord_8045410 prefixEnd_8045410 1377054130829824176691613 := by
  unfold tailWord_8045410
  simp only [CollatzResearch.WordTrace]
  refine ⟨73360052445715272869917421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195626806521907394319779789 73360052445715272869917421)
  ·
    refine ⟨27510019667143227326219033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73360052445715272869917421 27510019667143227326219033)
    ·
      refine ⟨20632514750357420494664275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27510019667143227326219033 20632514750357420494664275)
      ·
        refine ⟨30948772125536130741996413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20632514750357420494664275 30948772125536130741996413)
        ·
          refine ⟨11605789547076049028248655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30948772125536130741996413 11605789547076049028248655)
          ·
            refine ⟨17408684320614073542372983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11605789547076049028248655 17408684320614073542372983)
            ·
              refine ⟨26113026480921110313559475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17408684320614073542372983 26113026480921110313559475)
              ·
                refine ⟨39169539721381665470339213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26113026480921110313559475 39169539721381665470339213)
                ·
                  refine ⟨14688577395518124551377205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39169539721381665470339213 14688577395518124551377205)
                  ·
                    refine ⟨1377054130829824176691613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14688577395518124551377205 1377054130829824176691613)
                    ·
                      rfl

theorem cell23_8045410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 1, 3, 5].length) (baseStart_8045410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045410 prefixEnd_8045410 := by exact prefixLift 8045410
  have htrace : WordTrace (prefixWord ++ tailWord_8045410) baseStart_8045410 baseEnd_8045410 := by
    simpa [prefixWord, tailWord_8045410, baseEnd_8045410] using wordTrace_append hprefix tailTrace_8045410
  have hstable : (prefixWord ++ tailWord_8045410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045410).length < 2 ^ (prefixWord ++ tailWord_8045410).sum := by decide
  have hdescent : baseEnd_8045410 < baseStart_8045410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045413 : List Nat := [1, 3, 1, 3, 1, 1, 2, 1, 2, 6, 2]
def baseStart_8045413 : Nat := 118140960795 + 8045413 * 2 ^ 59
def prefixEnd_8045413 : Nat := 4983230072969 + 3 ^ 40 * 8045413 * 2
def baseEnd_8045413 : Nat := 4131163932931436018337325

theorem tailTrace_8045413 : CollatzResearch.WordTrace tailWord_8045413 prefixEnd_8045413 4131163932931436018337325 := by
  unfold tailWord_8045413
  simp only [CollatzResearch.WordTrace]
  refine ⟨293440319201850222992028893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195626879467900148661352595 293440319201850222992028893)
  ·
    refine ⟨110040119700693833622010835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293440319201850222992028893 110040119700693833622010835)
    ·
      refine ⟨165060179551040750433016253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110040119700693833622010835 165060179551040750433016253)
      ·
        refine ⟨61897567331640281412381095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165060179551040750433016253 61897567331640281412381095)
        ·
          refine ⟨92846350997460422118571643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61897567331640281412381095 92846350997460422118571643)
          ·
            refine ⟨139269526496190633177857465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92846350997460422118571643 139269526496190633177857465)
            ·
              refine ⟨104452144872142974883393099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139269526496190633177857465 104452144872142974883393099)
              ·
                refine ⟨156678217308214462325089649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104452144872142974883393099 156678217308214462325089649)
                ·
                  refine ⟨117508662981160846743817237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156678217308214462325089649 117508662981160846743817237)
                  ·
                    refine ⟨5508218577241914691116433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117508662981160846743817237 5508218577241914691116433)
                    ·
                      refine ⟨4131163932931436018337325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508218577241914691116433 4131163932931436018337325)
                      ·
                        rfl

theorem cell23_8045413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 6, 2].length) (baseStart_8045413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045413 prefixEnd_8045413 := by exact prefixLift 8045413
  have htrace : WordTrace (prefixWord ++ tailWord_8045413) baseStart_8045413 baseEnd_8045413 := by
    simpa [prefixWord, tailWord_8045413, baseEnd_8045413] using wordTrace_append hprefix tailTrace_8045413
  have hstable : (prefixWord ++ tailWord_8045413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045413).length < 2 ^ (prefixWord ++ tailWord_8045413).sum := by decide
  have hdescent : baseEnd_8045413 < baseStart_8045413 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045433 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 5]
def baseStart_8045433 : Nat := 118140960795 + 8045433 * 2 ^ 59
def prefixEnd_8045433 : Nat := 4983230072969 + 3 ^ 40 * 8045433 * 2
def baseEnd_8045433 : Nat := 4131174202544525940087233

theorem tailTrace_8045433 : CollatzResearch.WordTrace tailWord_8045433 prefixEnd_8045433 4131174202544525940087233 := by
  unfold tailWord_8045433
  simp only [CollatzResearch.WordTrace]
  refine ⟨293441048661777766407756953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195627365774518510938504635 293441048661777766407756953)
  ·
    refine ⟨220080786496333324805817715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293441048661777766407756953 220080786496333324805817715)
    ·
      refine ⟨330121179744499987208726573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220080786496333324805817715 330121179744499987208726573)
      ·
        refine ⟨123795442404187495203272465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330121179744499987208726573 123795442404187495203272465)
        ·
          refine ⟨92846581803140621402454349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123795442404187495203272465 92846581803140621402454349)
          ·
            refine ⟨34817468176177733025920381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92846581803140621402454349 34817468176177733025920381)
            ·
              refine ⟨13056550566066649884720143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34817468176177733025920381 13056550566066649884720143)
              ·
                refine ⟨19584825849099974827080215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13056550566066649884720143 19584825849099974827080215)
                ·
                  refine ⟨29377238773649962240620323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19584825849099974827080215 29377238773649962240620323)
                  ·
                    refine ⟨44065858160474943360930485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29377238773649962240620323 44065858160474943360930485)
                    ·
                      refine ⟨4131174202544525940087233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44065858160474943360930485 4131174202544525940087233)
                      ·
                        rfl

theorem cell23_8045433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 1, 1, 5].length) (baseStart_8045433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045433 prefixEnd_8045433 := by exact prefixLift 8045433
  have htrace : WordTrace (prefixWord ++ tailWord_8045433) baseStart_8045433 baseEnd_8045433 := by
    simpa [prefixWord, tailWord_8045433, baseEnd_8045433] using wordTrace_append hprefix tailTrace_8045433
  have hstable : (prefixWord ++ tailWord_8045433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045433).length < 2 ^ (prefixWord ++ tailWord_8045433).sum := by decide
  have hdescent : baseEnd_8045433 < baseStart_8045433 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045450 : List Nat := [3, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3]
def baseStart_8045450 : Nat := 118140960795 + 8045450 * 2 ^ 59
def prefixEnd_8045450 : Nat := 4983230072969 + 3 ^ 40 * 8045450 * 2
def baseEnd_8045450 : Nat := 4131182931715652373574655

theorem tailTrace_8045450 : CollatzResearch.WordTrace tailWord_8045450 prefixEnd_8045450 4131182931715652373574655 := by
  unfold tailWord_8045450
  simp only [CollatzResearch.WordTrace]
  refine ⟨73360417175679044577781451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195627779135144118874083869 73360417175679044577781451)
  ·
    refine ⟨110040625763518566866672177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73360417175679044577781451 110040625763518566866672177)
    ·
      refine ⟨82530469322638925150004133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110040625763518566866672177 82530469322638925150004133)
      ·
        refine ⟨15474462997994798465625775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82530469322638925150004133 15474462997994798465625775)
        ·
          refine ⟨23211694496992197698438663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15474462997994798465625775 23211694496992197698438663)
          ·
            refine ⟨34817541745488296547657995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23211694496992197698438663 34817541745488296547657995)
            ·
              refine ⟨52226312618232444821486993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34817541745488296547657995 52226312618232444821486993)
              ·
                refine ⟨39169734463674333616115245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52226312618232444821486993 39169734463674333616115245)
                ·
                  refine ⟨14688650423877875106043217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39169734463674333616115245 14688650423877875106043217)
                  ·
                    refine ⟨11016487817908406329532413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14688650423877875106043217 11016487817908406329532413)
                    ·
                      refine ⟨4131182931715652373574655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11016487817908406329532413 4131182931715652373574655)
                      ·
                        rfl

theorem cell23_8045450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_8045450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045450 prefixEnd_8045450 := by exact prefixLift 8045450
  have htrace : WordTrace (prefixWord ++ tailWord_8045450) baseStart_8045450 baseEnd_8045450 := by
    simpa [prefixWord, tailWord_8045450, baseEnd_8045450] using wordTrace_append hprefix tailTrace_8045450
  have hstable : (prefixWord ++ tailWord_8045450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045450).length < 2 ^ (prefixWord ++ tailWord_8045450).sum := by decide
  have hdescent : baseEnd_8045450 < baseStart_8045450 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045460 : List Nat := [2, 4, 2, 1, 1, 1, 4, 1, 1, 2, 4]
def baseStart_8045460 : Nat := 118140960795 + 8045460 * 2 ^ 59
def prefixEnd_8045460 : Nat := 4983230072969 + 3 ^ 40 * 8045460 * 2
def baseEnd_8045460 : Nat := 4131188066522197334449609

theorem tailTrace_8045460 : CollatzResearch.WordTrace tailWord_8045460 prefixEnd_8045460 4131188066522197334449609 := by
  unfold tailWord_8045460
  simp only [CollatzResearch.WordTrace]
  refine ⟨146721016716339975009494917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195628022288453300012659889 146721016716339975009494917)
  ·
    refine ⟨27510190634313745314280297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146721016716339975009494917 27510190634313745314280297)
    ·
      refine ⟨20632642975735308985710223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27510190634313745314280297 20632642975735308985710223)
      ·
        refine ⟨30948964463602963478565335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20632642975735308985710223 30948964463602963478565335)
        ·
          refine ⟨46423446695404445217848003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30948964463602963478565335 46423446695404445217848003)
          ·
            refine ⟨69635170043106667826772005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46423446695404445217848003 69635170043106667826772005)
            ·
              refine ⟨13056594383082500217519751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69635170043106667826772005 13056594383082500217519751)
              ·
                refine ⟨19584891574623750326279627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13056594383082500217519751 19584891574623750326279627)
                ·
                  refine ⟨29377337361935625489419441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19584891574623750326279627 29377337361935625489419441)
                  ·
                    refine ⟨22033003021451719117064581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29377337361935625489419441 22033003021451719117064581)
                    ·
                      refine ⟨4131188066522197334449609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22033003021451719117064581 4131188066522197334449609)
                      ·
                        rfl

theorem cell23_8045460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 1, 2, 4].length) (baseStart_8045460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045460 prefixEnd_8045460 := by exact prefixLift 8045460
  have htrace : WordTrace (prefixWord ++ tailWord_8045460) baseStart_8045460 baseEnd_8045460 := by
    simpa [prefixWord, tailWord_8045460, baseEnd_8045460] using wordTrace_append hprefix tailTrace_8045460
  have hstable : (prefixWord ++ tailWord_8045460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045460).length < 2 ^ (prefixWord ++ tailWord_8045460).sum := by decide
  have hdescent : baseEnd_8045460 < baseStart_8045460 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045497 : List Nat := [1, 2, 1, 4, 2, 2, 3, 2, 2, 1, 3]
def baseStart_8045497 : Nat := 118140960795 + 8045497 * 2 ^ 59
def prefixEnd_8045497 : Nat := 4983230072969 + 3 ^ 40 * 8045497 * 2
def baseEnd_8045497 : Nat := 4131207065306413689686939

theorem tailTrace_8045497 : CollatzResearch.WordTrace tailWord_8045497 prefixEnd_8045497 4131207065306413689686939 := by
  unfold tailWord_8045497
  simp only [CollatzResearch.WordTrace]
  refine ⟨293443382933545905338086745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195628921955697270225391163 293443382933545905338086745)
  ·
    refine ⟨220082537200159429003565059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293443382933545905338086745 220082537200159429003565059)
    ·
      refine ⟨330123805800239143505347589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220082537200159429003565059 330123805800239143505347589)
      ·
        refine ⟨61898213587544839407252673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330123805800239143505347589 61898213587544839407252673)
        ·
          refine ⟨46423660190658629555439505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61898213587544839407252673 46423660190658629555439505)
          ·
            refine ⟨34817745142993972166579629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46423660190658629555439505 34817745142993972166579629)
            ·
              refine ⟨13056654428622739562467361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34817745142993972166579629 13056654428622739562467361)
              ·
                refine ⟨9792490821467054671850521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13056654428622739562467361 9792490821467054671850521)
                ·
                  refine ⟨7344368116100291003887891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9792490821467054671850521 7344368116100291003887891)
                  ·
                    refine ⟨11016552174150436505831837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7344368116100291003887891 11016552174150436505831837)
                    ·
                      refine ⟨4131207065306413689686939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11016552174150436505831837 4131207065306413689686939)
                      ·
                        rfl

theorem cell23_8045497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_8045497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045497 prefixEnd_8045497 := by exact prefixLift 8045497
  have htrace : WordTrace (prefixWord ++ tailWord_8045497) baseStart_8045497 baseEnd_8045497 := by
    simpa [prefixWord, tailWord_8045497, baseEnd_8045497] using wordTrace_append hprefix tailTrace_8045497
  have hstable : (prefixWord ++ tailWord_8045497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045497).length < 2 ^ (prefixWord ++ tailWord_8045497).sum := by decide
  have hdescent : baseEnd_8045497 < baseStart_8045497 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045524 : List Nat := [2, 4, 1, 2, 1, 3, 2, 2, 1, 3, 2]
def baseStart_8045524 : Nat := 118140960795 + 8045524 * 2 ^ 59
def prefixEnd_8045524 : Nat := 4983230072969 + 3 ^ 40 * 8045524 * 2
def baseEnd_8045524 : Nat := 4131220929284085084049315

theorem tailTrace_8045524 : CollatzResearch.WordTrace tailWord_8045524 prefixEnd_8045524 4131220929284085084049315 := by
  unfold tailWord_8045524
  simp only [CollatzResearch.WordTrace]
  refine ⟨146722183852224044474659813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195629578469632059299546417 146722183852224044474659813)
  ·
    refine ⟨27510409472292008338998715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146722183852224044474659813 27510409472292008338998715)
    ·
      refine ⟨41265614208438012508498073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27510409472292008338998715 41265614208438012508498073)
      ·
        refine ⟨30949210656328509381373555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41265614208438012508498073 30949210656328509381373555)
        ·
          refine ⟨46423815984492764072060333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30949210656328509381373555 46423815984492764072060333)
          ·
            refine ⟨17408930994184786527022625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 46423815984492764072060333 17408930994184786527022625)
            ·
              refine ⟨13056698245638589895266969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17408930994184786527022625 13056698245638589895266969)
              ·
                refine ⟨9792523684228942421450227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13056698245638589895266969 9792523684228942421450227)
                ·
                  refine ⟨14688785526343413632175341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9792523684228942421450227 14688785526343413632175341)
                  ·
                    refine ⟨5508294572378780112065753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14688785526343413632175341 5508294572378780112065753)
                    ·
                      refine ⟨4131220929284085084049315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508294572378780112065753 4131220929284085084049315)
                      ·
                        rfl

theorem cell23_8045524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_8045524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045524 prefixEnd_8045524 := by exact prefixLift 8045524
  have htrace : WordTrace (prefixWord ++ tailWord_8045524) baseStart_8045524 baseEnd_8045524 := by
    simpa [prefixWord, tailWord_8045524, baseEnd_8045524] using wordTrace_append hprefix tailTrace_8045524
  have hstable : (prefixWord ++ tailWord_8045524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045524).length < 2 ^ (prefixWord ++ tailWord_8045524).sum := by decide
  have hdescent : baseEnd_8045524 < baseStart_8045524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045573 : List Nat := [1, 3, 1, 1, 2, 3, 1, 2, 4, 5]
def baseStart_8045573 : Nat := 118140960795 + 8045573 * 2 ^ 59
def prefixEnd_8045573 : Nat := 4983230072969 + 3 ^ 40 * 8045573 * 2
def baseEnd_8045573 : Nat := 1377082029945385130778863

theorem tailTrace_8045573 : CollatzResearch.WordTrace tailWord_8045573 prefixEnd_8045573 1377082029945385130778863 := by
  unfold tailWord_8045573
  simp only [CollatzResearch.WordTrace]
  refine ⟨293446154881270570317853373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195630769920847046878568915 293446154881270570317853373)
  ·
    refine ⟨110042308080476463869195015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293446154881270570317853373 110042308080476463869195015)
    ·
      refine ⟨165063462120714695803792523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110042308080476463869195015 165063462120714695803792523)
      ·
        refine ⟨247595193181072043705688785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165063462120714695803792523 247595193181072043705688785)
        ·
          refine ⟨185696394885804032779266589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247595193181072043705688785 185696394885804032779266589)
          ·
            refine ⟨69636148082176512292224971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185696394885804032779266589 69636148082176512292224971)
            ·
              refine ⟨104454222123264768438337457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69636148082176512292224971 104454222123264768438337457)
              ·
                refine ⟨78340666592448576328753093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104454222123264768438337457 78340666592448576328753093)
                ·
                  refine ⟨14688874986084108061641205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78340666592448576328753093 14688874986084108061641205)
                  ·
                    refine ⟨1377082029945385130778863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14688874986084108061641205 1377082029945385130778863)
                    ·
                      rfl

theorem cell23_8045573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 2, 4, 5].length) (baseStart_8045573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045573 prefixEnd_8045573 := by exact prefixLift 8045573
  have htrace : WordTrace (prefixWord ++ tailWord_8045573) baseStart_8045573 baseEnd_8045573 := by
    simpa [prefixWord, tailWord_8045573, baseEnd_8045573] using wordTrace_append hprefix tailTrace_8045573
  have hstable : (prefixWord ++ tailWord_8045573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045573).length < 2 ^ (prefixWord ++ tailWord_8045573).sum := by decide
  have hdescent : baseEnd_8045573 < baseStart_8045573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045593 : List Nat := [1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 4]
def baseStart_8045593 : Nat := 118140960795 + 8045593 * 2 ^ 59
def prefixEnd_8045593 : Nat := 4983230072969 + 3 ^ 40 * 8045593 * 2
def baseEnd_8045593 : Nat := 4131256359449245314086497

theorem tailTrace_8045593 : CollatzResearch.WordTrace tailWord_8045593 prefixEnd_8045593 4131256359449245314086497 := by
  unfold tailWord_8045593
  simp only [CollatzResearch.WordTrace]
  refine ⟨293446884341198113733581433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195631256227465409155720955 293446884341198113733581433)
  ·
    refine ⟨220085163255898585300186075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293446884341198113733581433 220085163255898585300186075)
    ·
      refine ⟨330127744883847877950279113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220085163255898585300186075 330127744883847877950279113)
      ·
        refine ⟨247595808662885908462709335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330127744883847877950279113 247595808662885908462709335)
        ·
          refine ⟨371393712994328862694064003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247595808662885908462709335 371393712994328862694064003)
          ·
            refine ⟨557090569491493294041096005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371393712994328862694064003 557090569491493294041096005)
            ·
              refine ⟨104454481779654992632705501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 557090569491493294041096005 104454481779654992632705501)
              ·
                refine ⟨39170430667370622237264563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104454481779654992632705501 39170430667370622237264563)
                ·
                  refine ⟨58755646001055933355896845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39170430667370622237264563 58755646001055933355896845)
                  ·
                    refine ⟨22033367250395975008461317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 58755646001055933355896845 22033367250395975008461317)
                    ·
                      refine ⟨4131256359449245314086497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22033367250395975008461317 4131256359449245314086497)
                      ·
                        rfl

theorem cell23_8045593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 3, 1, 3, 4].length) (baseStart_8045593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045593 prefixEnd_8045593 := by exact prefixLift 8045593
  have htrace : WordTrace (prefixWord ++ tailWord_8045593) baseStart_8045593 baseEnd_8045593 := by
    simpa [prefixWord, tailWord_8045593, baseEnd_8045593] using wordTrace_append hprefix tailTrace_8045593
  have hstable : (prefixWord ++ tailWord_8045593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045593).length < 2 ^ (prefixWord ++ tailWord_8045593).sum := by decide
  have hdescent : baseEnd_8045593 < baseStart_8045593 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045607 : List Nat := [1, 1, 7, 1, 1, 1, 2, 2, 2, 5]
def baseStart_8045607 : Nat := 118140960795 + 8045607 * 2 ^ 59
def prefixEnd_8045607 : Nat := 4983230072969 + 3 ^ 40 * 8045607 * 2
def baseEnd_8045607 : Nat := 1377087849392802753103811

theorem tailTrace_8045607 : CollatzResearch.WordTrace tailWord_8045607 prefixEnd_8045607 1377087849392802753103811 := by
  unfold tailWord_8045607
  simp only [CollatzResearch.WordTrace]
  refine ⟨293447394963147394124591075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195631596642098262749727383 293447394963147394124591075)
  ·
    refine ⟨440171092444721091186886613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293447394963147394124591075 440171092444721091186886613)
    ·
      refine ⟨10316509979173150574692655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 440171092444721091186886613 10316509979173150574692655)
      ·
        refine ⟨15474764968759725862038983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10316509979173150574692655 15474764968759725862038983)
        ·
          refine ⟨23212147453139588793058475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15474764968759725862038983 23212147453139588793058475)
          ·
            refine ⟨34818221179709383189587713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23212147453139588793058475 34818221179709383189587713)
            ·
              refine ⟨26113665884782037392190785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34818221179709383189587713 26113665884782037392190785)
              ·
                refine ⟨19585249413586528044143089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26113665884782037392190785 19585249413586528044143089)
                ·
                  refine ⟨14688937060189896033107317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19585249413586528044143089 14688937060189896033107317)
                  ·
                    refine ⟨1377087849392802753103811, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14688937060189896033107317 1377087849392802753103811)
                    ·
                      rfl

theorem cell23_8045607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_8045607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045607 prefixEnd_8045607 := by exact prefixLift 8045607
  have htrace : WordTrace (prefixWord ++ tailWord_8045607) baseStart_8045607 baseEnd_8045607 := by
    simpa [prefixWord, tailWord_8045607, baseEnd_8045607] using wordTrace_append hprefix tailTrace_8045607
  have hstable : (prefixWord ++ tailWord_8045607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045607).length < 2 ^ (prefixWord ++ tailWord_8045607).sum := by decide
  have hdescent : baseEnd_8045607 < baseStart_8045607 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045623 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 4]
def baseStart_8045623 : Nat := 118140960795 + 8045623 * 2 ^ 59
def prefixEnd_8045623 : Nat := 4983230072969 + 3 ^ 40 * 8045623 * 2
def baseEnd_8045623 : Nat := 4131271763868880196711359

theorem tailTrace_8045623 : CollatzResearch.WordTrace tailWord_8045623 prefixEnd_8045623 4131271763868880196711359 := by
  unfold tailWord_8045623
  simp only [CollatzResearch.WordTrace]
  refine ⟨293447978531089428857173523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195631985687392952571449015 293447978531089428857173523)
  ·
    refine ⟨440171967796634143285760285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293447978531089428857173523 440171967796634143285760285)
    ·
      refine ⟨165064487923737803732160107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440171967796634143285760285 165064487923737803732160107)
      ·
        refine ⟨247596731885606705598240161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165064487923737803732160107 247596731885606705598240161)
        ·
          refine ⟨185697548914205029198680121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247596731885606705598240161 185697548914205029198680121)
          ·
            refine ⟨139273161685653771899010091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185697548914205029198680121 139273161685653771899010091)
            ·
              refine ⟨208909742528480657848515137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139273161685653771899010091 208909742528480657848515137)
              ·
                refine ⟨156682306896360493386386353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208909742528480657848515137 156682306896360493386386353)
                ·
                  refine ⟨117511730172270370039789765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156682306896360493386386353 117511730172270370039789765)
                  ·
                    refine ⟨22033449407300694382460581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 117511730172270370039789765 22033449407300694382460581)
                    ·
                      refine ⟨4131271763868880196711359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22033449407300694382460581 4131271763868880196711359)
                      ·
                        rfl

theorem cell23_8045623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 4, 4].length) (baseStart_8045623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045623 prefixEnd_8045623 := by exact prefixLift 8045623
  have htrace : WordTrace (prefixWord ++ tailWord_8045623) baseStart_8045623 baseEnd_8045623 := by
    simpa [prefixWord, tailWord_8045623, baseEnd_8045623] using wordTrace_append hprefix tailTrace_8045623
  have hstable : (prefixWord ++ tailWord_8045623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045623).length < 2 ^ (prefixWord ++ tailWord_8045623).sum := by decide
  have hdescent : baseEnd_8045623 < baseStart_8045623 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045697 : List Nat := [1, 2, 4, 2, 2, 1, 1, 4, 1, 5]
def baseStart_8045697 : Nat := 118140960795 + 8045697 * 2 ^ 59
def prefixEnd_8045697 : Nat := 4983230072969 + 3 ^ 40 * 8045697 * 2
def baseEnd_8045697 : Nat := 1377103253812437635728673

theorem tailTrace_8045697 : CollatzResearch.WordTrace tailWord_8045697 prefixEnd_8045697 1377103253812437635728673 := by
  unfold tailWord_8045697
  simp only [CollatzResearch.WordTrace]
  refine ⟨293450677532821339495367345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195633785021880892996911563 293450677532821339495367345)
  ·
    refine ⟨220088008149616004621525509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293450677532821339495367345 220088008149616004621525509)
    ·
      refine ⟨41266501528053000866536033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220088008149616004621525509 41266501528053000866536033)
      ·
        refine ⟨30949876146039750649902025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41266501528053000866536033 30949876146039750649902025)
        ·
          refine ⟨23212407109529812987426519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30949876146039750649902025 23212407109529812987426519)
          ·
            refine ⟨34818610664294719481139779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23212407109529812987426519 34818610664294719481139779)
            ·
              refine ⟨52227915996442079221709669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34818610664294719481139779 52227915996442079221709669)
              ·
                refine ⟨9792734249332889854070563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52227915996442079221709669 9792734249332889854070563)
                ·
                  refine ⟨14689101373999334781105845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9792734249332889854070563 14689101373999334781105845)
                  ·
                    refine ⟨1377103253812437635728673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14689101373999334781105845 1377103253812437635728673)
                    ·
                      rfl

theorem cell23_8045697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_8045697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045697 prefixEnd_8045697 := by exact prefixLift 8045697
  have htrace : WordTrace (prefixWord ++ tailWord_8045697) baseStart_8045697 baseEnd_8045697 := by
    simpa [prefixWord, tailWord_8045697, baseEnd_8045697] using wordTrace_append hprefix tailTrace_8045697
  have hstable : (prefixWord ++ tailWord_8045697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045697).length < 2 ^ (prefixWord ++ tailWord_8045697).sum := by decide
  have hdescent : baseEnd_8045697 < baseStart_8045697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045764 : List Nat := [2, 3, 3, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_8045764 : Nat := 118140960795 + 8045764 * 2 ^ 59
def prefixEnd_8045764 : Nat := 4983230072969 + 3 ^ 40 * 8045764 * 2
def baseEnd_8045764 : Nat := 4131344164641164145048211

theorem tailTrace_8045764 : CollatzResearch.WordTrace tailWord_8045764 prefixEnd_8045764 4131344164641164145048211 := by
  unfold tailWord_8045764
  simp only [CollatzResearch.WordTrace]
  refine ⟨146726560611789304969028173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195635414149052406625370897 146726560611789304969028173)
  ·
    refine ⟨55022460229420989363385565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146726560611789304969028173 55022460229420989363385565)
    ·
      refine ⟨20633422586032871011269587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55022460229420989363385565 20633422586032871011269587)
      ·
        refine ⟨30950133879049306516904381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20633422586032871011269587 30950133879049306516904381)
        ·
          refine ⟨11606300204643489943839143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30950133879049306516904381 11606300204643489943839143)
          ·
            refine ⟨17409450306965234915758715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11606300204643489943839143 17409450306965234915758715)
            ·
              refine ⟨26114175460447852373638073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17409450306965234915758715 26114175460447852373638073)
              ·
                refine ⟨19585631595335889280228555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26114175460447852373638073 19585631595335889280228555)
                ·
                  refine ⟨29378447393003833920342833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19585631595335889280228555 29378447393003833920342833)
                  ·
                    refine ⟨22033835544752875440257125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29378447393003833920342833 22033835544752875440257125)
                    ·
                      refine ⟨4131344164641164145048211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22033835544752875440257125 4131344164641164145048211)
                      ·
                        rfl

theorem cell23_8045764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_8045764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045764 prefixEnd_8045764 := by exact prefixLift 8045764
  have htrace : WordTrace (prefixWord ++ tailWord_8045764) baseStart_8045764 baseEnd_8045764 := by
    simpa [prefixWord, tailWord_8045764, baseEnd_8045764] using wordTrace_append hprefix tailTrace_8045764
  have hstable : (prefixWord ++ tailWord_8045764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045764).length < 2 ^ (prefixWord ++ tailWord_8045764).sum := by decide
  have hdescent : baseEnd_8045764 < baseStart_8045764 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045767 : List Nat := [1, 1, 4, 1, 1, 1, 1, 3, 6, 1, 3]
def baseStart_8045767 : Nat := 118140960795 + 8045767 * 2 ^ 59
def prefixEnd_8045767 : Nat := 4983230072969 + 3 ^ 40 * 8045767 * 2
def baseEnd_8045767 : Nat := 4131345705083127633310697

theorem tailTrace_8045767 : CollatzResearch.WordTrace tailWord_8045767 prefixEnd_8045767 4131345705083127633310697 := by
  unfold tailWord_8045767
  simp only [CollatzResearch.WordTrace]
  refine ⟨293453230642567741450415555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195635487095045160966943703 293453230642567741450415555)
  ·
    refine ⟨440179845963851612175623333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293453230642567741450415555 440179845963851612175623333)
    ·
      refine ⟨82533721118222177282929375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440179845963851612175623333 82533721118222177282929375)
      ·
        refine ⟨123800581677333265924394063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82533721118222177282929375 123800581677333265924394063)
        ·
          refine ⟨185700872515999898886591095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123800581677333265924394063 185700872515999898886591095)
          ·
            refine ⟨278551308773999848329886643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185700872515999898886591095 278551308773999848329886643)
            ·
              refine ⟨417826963160999772494829965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278551308773999848329886643 417826963160999772494829965)
              ·
                refine ⟨156685111185374914685561237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417826963160999772494829965 156685111185374914685561237)
                ·
                  refine ⟨7344614586814449125885683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 156685111185374914685561237 7344614586814449125885683)
                  ·
                    refine ⟨11016921880221673688828525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7344614586814449125885683 11016921880221673688828525)
                    ·
                      refine ⟨4131345705083127633310697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11016921880221673688828525 4131345705083127633310697)
                      ·
                        rfl

theorem cell23_8045767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_8045767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045767 prefixEnd_8045767 := by exact prefixLift 8045767
  have htrace : WordTrace (prefixWord ++ tailWord_8045767) baseStart_8045767 baseEnd_8045767 := by
    simpa [prefixWord, tailWord_8045767, baseEnd_8045767] using wordTrace_append hprefix tailTrace_8045767
  have hstable : (prefixWord ++ tailWord_8045767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045767).length < 2 ^ (prefixWord ++ tailWord_8045767).sum := by decide
  have hdescent : baseEnd_8045767 < baseStart_8045767 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045824 : List Nat := [2, 1, 1, 2, 1, 1, 3, 4, 4, 2, 2]
def baseStart_8045824 : Nat := 118140960795 + 8045824 * 2 ^ 59
def prefixEnd_8045824 : Nat := 4983230072969 + 3 ^ 40 * 8045824 * 2
def baseEnd_8045824 : Nat := 4131374973480433910297935

theorem tailTrace_8045824 : CollatzResearch.WordTrace tailWord_8045824 prefixEnd_8045824 4131374973480433910297935 := by
  unfold tailWord_8045824
  simp only [CollatzResearch.WordTrace]
  refine ⟨146727654801680620092620263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195636873068907493456827017 146727654801680620092620263)
  ·
    refine ⟨220091482202520930138930395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146727654801680620092620263 220091482202520930138930395)
    ·
      refine ⟨330137223303781395208395593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220091482202520930138930395 330137223303781395208395593)
      ·
        refine ⟨247602917477836046406296695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330137223303781395208395593 247602917477836046406296695)
        ·
          refine ⟨371404376216754069609445043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247602917477836046406296695 371404376216754069609445043)
          ·
            refine ⟨557106564325131104414167565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371404376216754069609445043 557106564325131104414167565)
            ·
              refine ⟨208914961621924164155312837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 557106564325131104414167565 208914961621924164155312837)
              ·
                refine ⟨39171555304110780779121157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 208914961621924164155312837 39171555304110780779121157)
                ·
                  refine ⟨7344666619520771396085217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39171555304110780779121157 7344666619520771396085217)
                  ·
                    refine ⟨5508499964640578547063913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7344666619520771396085217 5508499964640578547063913)
                    ·
                      refine ⟨4131374973480433910297935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508499964640578547063913 4131374973480433910297935)
                      ·
                        rfl

theorem cell23_8045824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 4, 4, 2, 2].length) (baseStart_8045824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045824 prefixEnd_8045824 := by exact prefixLift 8045824
  have htrace : WordTrace (prefixWord ++ tailWord_8045824) baseStart_8045824 baseEnd_8045824 := by
    simpa [prefixWord, tailWord_8045824, baseEnd_8045824] using wordTrace_append hprefix tailTrace_8045824
  have hstable : (prefixWord ++ tailWord_8045824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045824).length < 2 ^ (prefixWord ++ tailWord_8045824).sum := by decide
  have hdescent : baseEnd_8045824 < baseStart_8045824 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045828 : List Nat := [2, 3, 2, 2, 2, 1, 4, 1, 1, 3, 2]
def baseStart_8045828 : Nat := 118140960795 + 8045828 * 2 ^ 59
def prefixEnd_8045828 : Nat := 4983230072969 + 3 ^ 40 * 8045828 * 2
def baseEnd_8045828 : Nat := 4131377027403051894647917

theorem tailTrace_8045828 : CollatzResearch.WordTrace tailWord_8045828 prefixEnd_8045828 4131377027403051894647917 := by
  unfold tailWord_8045828
  simp only [CollatzResearch.WordTrace]
  refine ⟨146727727747673374434193069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195636970330231165912257425 146727727747673374434193069)
  ·
    refine ⟨55022897905377515412822401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146727727747673374434193069 55022897905377515412822401)
    ·
      refine ⟨41267173429033136559616801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55022897905377515412822401 41267173429033136559616801)
      ·
        refine ⟨30950380071774852419712601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41267173429033136559616801 30950380071774852419712601)
        ·
          refine ⟨23212785053831139314784451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30950380071774852419712601 23212785053831139314784451)
          ·
            refine ⟨34819177580746708972176677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23212785053831139314784451 34819177580746708972176677)
            ·
              refine ⟨6528595796390007932283127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34819177580746708972176677 6528595796390007932283127)
              ·
                refine ⟨9792893694585011898424691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6528595796390007932283127 9792893694585011898424691)
                ·
                  refine ⟨14689340541877517847637037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9792893694585011898424691 14689340541877517847637037)
                  ·
                    refine ⟨5508502703204069192863889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14689340541877517847637037 5508502703204069192863889)
                    ·
                      refine ⟨4131377027403051894647917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508502703204069192863889 4131377027403051894647917)
                      ·
                        rfl

theorem cell23_8045828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_8045828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045828 prefixEnd_8045828 := by exact prefixLift 8045828
  have htrace : WordTrace (prefixWord ++ tailWord_8045828) baseStart_8045828 baseEnd_8045828 := by
    simpa [prefixWord, tailWord_8045828, baseEnd_8045828] using wordTrace_append hprefix tailTrace_8045828
  have hstable : (prefixWord ++ tailWord_8045828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045828).length < 2 ^ (prefixWord ++ tailWord_8045828).sum := by decide
  have hdescent : baseEnd_8045828 < baseStart_8045828 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045847 : List Nat := [1, 1, 3, 4, 1, 1, 4, 1, 7]
def baseStart_8045847 : Nat := 118140960795 + 8045847 * 2 ^ 59
def prefixEnd_8045847 : Nat := 4983230072969 + 3 ^ 40 * 8045847 * 2
def baseEnd_8045847 : Nat := 459042975948387480034481

theorem tailTrace_8045847 : CollatzResearch.WordTrace tailWord_8045847 prefixEnd_8045847 459042975948387480034481 := by
  unfold tailWord_8045847
  simp only [CollatzResearch.WordTrace]
  refine ⟨293456148482277915113327795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195637432321518610075551863 293456148482277915113327795)
  ·
    refine ⟨440184222723416872669991693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293456148482277915113327795 440184222723416872669991693)
    ·
      refine ⟨165069083521281327251246885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440184222723416872669991693 165069083521281327251246885)
      ·
        refine ⟨30950453160240248859608791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165069083521281327251246885 30950453160240248859608791)
        ·
          refine ⟨46425679740360373289413187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30950453160240248859608791 46425679740360373289413187)
          ·
            refine ⟨69638519610540559934119781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46425679740360373289413187 69638519610540559934119781)
            ·
              refine ⟨13057222426976354987647459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69638519610540559934119781 13057222426976354987647459)
              ·
                refine ⟨19585833640464532481471189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13057222426976354987647459 19585833640464532481471189)
                ·
                  refine ⟨459042975948387480034481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19585833640464532481471189 459042975948387480034481)
                  ·
                    rfl

theorem cell23_8045847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 1, 7].length) (baseStart_8045847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045847 prefixEnd_8045847 := by exact prefixLift 8045847
  have htrace : WordTrace (prefixWord ++ tailWord_8045847) baseStart_8045847 baseEnd_8045847 := by
    simpa [prefixWord, tailWord_8045847, baseEnd_8045847] using wordTrace_append hprefix tailTrace_8045847
  have hstable : (prefixWord ++ tailWord_8045847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045847).length < 2 ^ (prefixWord ++ tailWord_8045847).sum := by decide
  have hdescent : baseEnd_8045847 < baseStart_8045847 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045858 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 1, 4, 2]
def baseStart_8045858 : Nat := 118140960795 + 8045858 * 2 ^ 59
def prefixEnd_8045858 : Nat := 4983230072969 + 3 ^ 40 * 8045858 * 2
def baseEnd_8045858 : Nat := 4131392431822686777272779

theorem tailTrace_8045858 : CollatzResearch.WordTrace tailWord_8045858 prefixEnd_8045858 4131392431822686777272779 := by
  unfold tailWord_8045858
  simp only [CollatzResearch.WordTrace]
  refine ⟨73364137421309515997994557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195637699790158709327985485 73364137421309515997994557)
  ·
    refine ⟨27511551532991068499247959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 73364137421309515997994557 27511551532991068499247959)
    ·
      refine ⟨41267327299486602748871939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27511551532991068499247959 41267327299486602748871939)
      ·
        refine ⟨61900990949229904123307909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41267327299486602748871939 61900990949229904123307909)
        ·
          refine ⟨11606435802980607023120233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61900990949229904123307909 11606435802980607023120233)
          ·
            refine ⟨8704826852235455267340175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11606435802980607023120233 8704826852235455267340175)
            ·
              refine ⟨13057240278353182901010263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8704826852235455267340175 13057240278353182901010263)
              ·
                refine ⟨19585860417529774351515395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13057240278353182901010263 19585860417529774351515395)
                ·
                  refine ⟨29378790626294661527273093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19585860417529774351515395 29378790626294661527273093)
                  ·
                    refine ⟨5508523242430249036363705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29378790626294661527273093 5508523242430249036363705)
                    ·
                      refine ⟨4131392431822686777272779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508523242430249036363705 4131392431822686777272779)
                      ·
                        rfl

theorem cell23_8045858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_8045858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045858 prefixEnd_8045858 := by exact prefixLift 8045858
  have htrace : WordTrace (prefixWord ++ tailWord_8045858) baseStart_8045858 baseEnd_8045858 := by
    simpa [prefixWord, tailWord_8045858, baseEnd_8045858] using wordTrace_append hprefix tailTrace_8045858
  have hstable : (prefixWord ++ tailWord_8045858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045858).length < 2 ^ (prefixWord ++ tailWord_8045858).sum := by decide
  have hdescent : baseEnd_8045858 < baseStart_8045858 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045877 : List Nat := [1, 3, 3, 1, 2, 2, 2, 1, 1, 7]
def baseStart_8045877 : Nat := 118140960795 + 8045877 * 2 ^ 59
def prefixEnd_8045877 : Nat := 4983230072969 + 3 ^ 40 * 8045877 * 2
def baseEnd_8045877 : Nat := 1377134062651707400978397

theorem tailTrace_8045877 : CollatzResearch.WordTrace tailWord_8045877 prefixEnd_8045877 1377134062651707400978397 := by
  unfold tailWord_8045877
  simp only [CollatzResearch.WordTrace]
  refine ⟨293457242672169230236919885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195638161781446153491279923 293457242672169230236919885)
  ·
    refine ⟨110046466002063461338844957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293457242672169230236919885 110046466002063461338844957)
    ·
      refine ⟨41267424750773798002066859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110046466002063461338844957 41267424750773798002066859)
      ·
        refine ⟨61901137126160697003100289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41267424750773798002066859 61901137126160697003100289)
        ·
          refine ⟨46425852844620522752325217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61901137126160697003100289 46425852844620522752325217)
          ·
            refine ⟨34819389633465392064243913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46425852844620522752325217 34819389633465392064243913)
            ·
              refine ⟨26114542225099044048182935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34819389633465392064243913 26114542225099044048182935)
              ·
                refine ⟨39171813337648566072274403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26114542225099044048182935 39171813337648566072274403)
                ·
                  refine ⟨58757720006472849108411605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39171813337648566072274403 58757720006472849108411605)
                  ·
                    refine ⟨1377134062651707400978397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 58757720006472849108411605 1377134062651707400978397)
                    ·
                      rfl

theorem cell23_8045877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 1, 1, 7].length) (baseStart_8045877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045877 prefixEnd_8045877 := by exact prefixLift 8045877
  have htrace : WordTrace (prefixWord ++ tailWord_8045877) baseStart_8045877 baseEnd_8045877 := by
    simpa [prefixWord, tailWord_8045877, baseEnd_8045877] using wordTrace_append hprefix tailTrace_8045877
  have hstable : (prefixWord ++ tailWord_8045877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045877).length < 2 ^ (prefixWord ++ tailWord_8045877).sum := by decide
  have hdescent : baseEnd_8045877 < baseStart_8045877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045897 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 4]
def baseStart_8045897 : Nat := 118140960795 + 8045897 * 2 ^ 59
def prefixEnd_8045897 : Nat := 4983230072969 + 3 ^ 40 * 8045897 * 2
def baseEnd_8045897 : Nat := 4131412457568212124685099

theorem tailTrace_8045897 : CollatzResearch.WordTrace tailWord_8045897 prefixEnd_8045897 4131412457568212124685099 := by
  unfold tailWord_8045897
  simp only [CollatzResearch.WordTrace]
  refine ⟨293457972132096773652647945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195638648088064515768431963 293457972132096773652647945)
  ·
    refine ⟨220093479099072580239485959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293457972132096773652647945 220093479099072580239485959)
    ·
      refine ⟨330140218648608870359228939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220093479099072580239485959 330140218648608870359228939)
      ·
        refine ⟨495210327972913305538843409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330140218648608870359228939 495210327972913305538843409)
        ·
          refine ⟨371407745979684979154132557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495210327972913305538843409 371407745979684979154132557)
          ·
            refine ⟨139277904742381867182799709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371407745979684979154132557 139277904742381867182799709)
            ·
              refine ⟨52229214278393200193549891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139277904742381867182799709 52229214278393200193549891)
              ·
                refine ⟨78343821417589800290324837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52229214278393200193549891 78343821417589800290324837)
                ·
                  refine ⟨14689466515798087554435907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78343821417589800290324837 14689466515798087554435907)
                  ·
                    refine ⟨22034199773697131331653861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14689466515798087554435907 22034199773697131331653861)
                    ·
                      refine ⟨4131412457568212124685099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22034199773697131331653861 4131412457568212124685099)
                      ·
                        rfl

theorem cell23_8045897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 1, 4].length) (baseStart_8045897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045897 prefixEnd_8045897 := by exact prefixLift 8045897
  have htrace : WordTrace (prefixWord ++ tailWord_8045897) baseStart_8045897 baseEnd_8045897 := by
    simpa [prefixWord, tailWord_8045897, baseEnd_8045897] using wordTrace_append hprefix tailTrace_8045897
  have hstable : (prefixWord ++ tailWord_8045897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045897).length < 2 ^ (prefixWord ++ tailWord_8045897).sum := by decide
  have hdescent : baseEnd_8045897 < baseStart_8045897 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045914 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2]
def baseStart_8045914 : Nat := 118140960795 + 8045914 * 2 ^ 59
def prefixEnd_8045914 : Nat := 4983230072969 + 3 ^ 40 * 8045914 * 2
def baseEnd_8045914 : Nat := 4131421186739338558172521

theorem tailTrace_8045914 : CollatzResearch.WordTrace tailWord_8045914 prefixEnd_8045914 4131421186739338558172521 := by
  unfold tailWord_8045914
  simp only [CollatzResearch.WordTrace]
  refine ⟨73364648043258796389004199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195639061448690123704011197 73364648043258796389004199)
  ·
    refine ⟨110046972064888194583506299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73364648043258796389004199 110046972064888194583506299)
    ·
      refine ⟨165070458097332291875259449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110046972064888194583506299 165070458097332291875259449)
      ·
        refine ⟨123802843572999218906444587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165070458097332291875259449 123802843572999218906444587)
        ·
          refine ⟨185704265359498828359666881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123802843572999218906444587 185704265359498828359666881)
          ·
            refine ⟨139278199019624121269750161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185704265359498828359666881 139278199019624121269750161)
            ·
              refine ⟨104458649264718090952312621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139278199019624121269750161 104458649264718090952312621)
              ·
                refine ⟨39171993474269284107117233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104458649264718090952312621 39171993474269284107117233)
                ·
                  refine ⟨29378995105701963080337925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39171993474269284107117233 29378995105701963080337925)
                  ·
                    refine ⟨5508561582319118077563361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29378995105701963080337925 5508561582319118077563361)
                    ·
                      refine ⟨4131421186739338558172521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508561582319118077563361 4131421186739338558172521)
                      ·
                        rfl

theorem cell23_8045914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2].length) (baseStart_8045914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045914 prefixEnd_8045914 := by exact prefixLift 8045914
  have htrace : WordTrace (prefixWord ++ tailWord_8045914) baseStart_8045914 baseEnd_8045914 := by
    simpa [prefixWord, tailWord_8045914, baseEnd_8045914] using wordTrace_append hprefix tailTrace_8045914
  have hstable : (prefixWord ++ tailWord_8045914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045914).length < 2 ^ (prefixWord ++ tailWord_8045914).sum := by decide
  have hdescent : baseEnd_8045914 < baseStart_8045914 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045981 : List Nat := [1, 4, 2, 1, 3, 1, 1, 1, 5, 1, 3]
def baseStart_8045981 : Nat := 118140960795 + 8045981 * 2 ^ 59
def prefixEnd_8045981 : Nat := 4983230072969 + 3 ^ 40 * 8045981 * 2
def baseEnd_8045981 : Nat := 4131455589943189796034713

theorem tailTrace_8045981 : CollatzResearch.WordTrace tailWord_8045981 prefixEnd_8045981 4131455589943189796034713 := by
  unfold tailWord_8045981
  simp only [CollatzResearch.WordTrace]
  refine ⟨293461035863792455998705797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195640690575861637332470531 293461035863792455998705797)
  ·
    refine ⟨55023944224461085499757337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293461035863792455998705797 55023944224461085499757337)
    ·
      refine ⟨41267958168345814124818003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55023944224461085499757337 41267958168345814124818003)
      ·
        refine ⟨61901937252518721187227005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41267958168345814124818003 61901937252518721187227005)
        ·
          refine ⟨23213226469694520445210127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61901937252518721187227005 23213226469694520445210127)
          ·
            refine ⟨34819839704541780667815191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23213226469694520445210127 34819839704541780667815191)
            ·
              refine ⟨52229759556812671001722787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34819839704541780667815191 52229759556812671001722787)
              ·
                refine ⟨78344639335219006502584181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52229759556812671001722787 78344639335219006502584181)
                ·
                  refine ⟨7344809937676781859617267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78344639335219006502584181 7344809937676781859617267)
                  ·
                    refine ⟨11017214906515172789425901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7344809937676781859617267 11017214906515172789425901)
                    ·
                      refine ⟨4131455589943189796034713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11017214906515172789425901 4131455589943189796034713)
                      ·
                        rfl

theorem cell23_8045981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 1, 1, 5, 1, 3].length) (baseStart_8045981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045981 prefixEnd_8045981 := by exact prefixLift 8045981
  have htrace : WordTrace (prefixWord ++ tailWord_8045981) baseStart_8045981 baseEnd_8045981 := by
    simpa [prefixWord, tailWord_8045981, baseEnd_8045981] using wordTrace_append hprefix tailTrace_8045981
  have hstable : (prefixWord ++ tailWord_8045981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045981).length < 2 ^ (prefixWord ++ tailWord_8045981).sum := by decide
  have hdescent : baseEnd_8045981 < baseStart_8045981 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045984 : List Nat := [2, 1, 1, 4, 1, 2, 2, 4, 1, 5]
def baseStart_8045984 : Nat := 118140960795 + 8045984 * 2 ^ 59
def prefixEnd_8045984 : Nat := 4983230072969 + 3 ^ 40 * 8045984 * 2
def baseEnd_8045984 : Nat := 1377152376795051094765733

theorem tailTrace_8045984 : CollatzResearch.WordTrace tailWord_8045984 prefixEnd_8045984 1377152376795051094765733 := by
  unfold tailWord_8045984
  simp only [CollatzResearch.WordTrace]
  refine ⟨146730572641390793755532503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195640763521854391674043337 146730572641390793755532503)
  ·
    refine ⟨220095858962086190633298755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146730572641390793755532503 220095858962086190633298755)
    ·
      refine ⟨330143788443129285949948133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220095858962086190633298755 330143788443129285949948133)
      ·
        refine ⟨61901960333086741115615275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330143788443129285949948133 61901960333086741115615275)
        ·
          refine ⟨92852940499630111673422913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61901960333086741115615275 92852940499630111673422913)
          ·
            refine ⟨69639705374722583755067185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92852940499630111673422913 69639705374722583755067185)
            ·
              refine ⟨52229779031041937816300389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69639705374722583755067185 52229779031041937816300389)
              ·
                refine ⟨9793083568320363340556323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52229779031041937816300389 9793083568320363340556323)
                ·
                  refine ⟨14689625352480545010834485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9793083568320363340556323 14689625352480545010834485)
                  ·
                    refine ⟨1377152376795051094765733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14689625352480545010834485 1377152376795051094765733)
                    ·
                      rfl

theorem cell23_8045984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 2, 4, 1, 5].length) (baseStart_8045984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045984 prefixEnd_8045984 := by exact prefixLift 8045984
  have htrace : WordTrace (prefixWord ++ tailWord_8045984) baseStart_8045984 baseEnd_8045984 := by
    simpa [prefixWord, tailWord_8045984, baseEnd_8045984] using wordTrace_append hprefix tailTrace_8045984
  have hstable : (prefixWord ++ tailWord_8045984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045984).length < 2 ^ (prefixWord ++ tailWord_8045984).sum := by decide
  have hdescent : baseEnd_8045984 < baseStart_8045984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8045991 : List Nat := [1, 1, 6, 1, 1, 1, 3, 1, 1, 5, 2]
def baseStart_8045991 : Nat := 118140960795 + 8045991 * 2 ^ 59
def prefixEnd_8045991 : Nat := 4983230072969 + 3 ^ 40 * 8045991 * 2
def baseEnd_8045991 : Nat := 4131460724749734756909667

theorem tailTrace_8045991 : CollatzResearch.WordTrace tailWord_8045991 prefixEnd_8045991 4131460724749734756909667 := by
  unfold tailWord_8045991
  simp only [CollatzResearch.WordTrace]
  refine ⟨293461400593756227706569827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195640933729170818471046551 293461400593756227706569827)
  ·
    refine ⟨440192100890634341559854741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293461400593756227706569827 440192100890634341559854741)
    ·
      refine ⟨20634004729248484760618191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 440192100890634341559854741 20634004729248484760618191)
      ·
        refine ⟨30951007093872727140927287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20634004729248484760618191 30951007093872727140927287)
        ·
          refine ⟨46426510640809090711390931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30951007093872727140927287 46426510640809090711390931)
          ·
            refine ⟨69639765961213636067086397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46426510640809090711390931 69639765961213636067086397)
            ·
              refine ⟨26114912235455113525157399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69639765961213636067086397 26114912235455113525157399)
              ·
                refine ⟨39172368353182670287736099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26114912235455113525157399 39172368353182670287736099)
                ·
                  refine ⟨58758552529774005431604149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39172368353182670287736099 58758552529774005431604149)
                  ·
                    refine ⟨5508614299666313009212889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 58758552529774005431604149 5508614299666313009212889)
                    ·
                      refine ⟨4131460724749734756909667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508614299666313009212889 4131460724749734756909667)
                      ·
                        rfl

theorem cell23_8045991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_8045991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8045991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8045991 prefixEnd_8045991 := by exact prefixLift 8045991
  have htrace : WordTrace (prefixWord ++ tailWord_8045991) baseStart_8045991 baseEnd_8045991 := by
    simpa [prefixWord, tailWord_8045991, baseEnd_8045991] using wordTrace_append hprefix tailTrace_8045991
  have hstable : (prefixWord ++ tailWord_8045991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8045991).length < 2 ^ (prefixWord ++ tailWord_8045991).sum := by decide
  have hdescent : baseEnd_8045991 < baseStart_8045991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8045991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046024 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 1, 1, 5]
def baseStart_8046024 : Nat := 118140960795 + 8046024 * 2 ^ 59
def prefixEnd_8046024 : Nat := 4983230072969 + 3 ^ 40 * 8046024 * 2
def baseEnd_8046024 : Nat := 4131477669611333127797015

theorem tailTrace_8046024 : CollatzResearch.WordTrace tailWord_8046024 prefixEnd_8046024 4131477669611333127797015 := by
  unfold tailWord_8046024
  simp only [CollatzResearch.WordTrace]
  refine ⟨146731302101318337171260563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195641736135091116228347417 146731302101318337171260563)
  ·
    refine ⟨220096953151977505756890845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146731302101318337171260563 220096953151977505756890845)
    ·
      refine ⟨82536357431991564658834067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220096953151977505756890845 82536357431991564658834067)
      ·
        refine ⟨123804536147987346988251101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82536357431991564658834067 123804536147987346988251101)
        ·
          refine ⟨46426701055495255120594163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123804536147987346988251101 46426701055495255120594163)
          ·
            refine ⟨69640051583242882680891245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46426701055495255120594163 69640051583242882680891245)
            ·
              refine ⟨26115019343716081005334217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69640051583242882680891245 26115019343716081005334217)
              ·
                refine ⟨19586264507787060754000663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26115019343716081005334217 19586264507787060754000663)
                ·
                  refine ⟨29379396761680591131000995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19586264507787060754000663 29379396761680591131000995)
                  ·
                    refine ⟨44069095142520886696501493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29379396761680591131000995 44069095142520886696501493)
                    ·
                      refine ⟨4131477669611333127797015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44069095142520886696501493 4131477669611333127797015)
                      ·
                        rfl

theorem cell23_8046024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_8046024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046024 prefixEnd_8046024 := by exact prefixLift 8046024
  have htrace : WordTrace (prefixWord ++ tailWord_8046024) baseStart_8046024 baseEnd_8046024 := by
    simpa [prefixWord, tailWord_8046024, baseEnd_8046024] using wordTrace_append hprefix tailTrace_8046024
  have hstable : (prefixWord ++ tailWord_8046024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046024).length < 2 ^ (prefixWord ++ tailWord_8046024).sum := by decide
  have hdescent : baseEnd_8046024 < baseStart_8046024 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046038 : List Nat := [5, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_8046038 : Nat := 118140960795 + 8046038 * 2 ^ 59
def prefixEnd_8046038 : Nat := 4983230072969 + 3 ^ 40 * 8046038 * 2
def baseEnd_8046038 : Nat := 4131484858340496073021951

theorem tailTrace_8046038 : CollatzResearch.WordTrace tailWord_8046038 prefixEnd_8046038 4131484858340496073021951 := by
  unfold tailWord_8046038
  simp only [CollatzResearch.WordTrace]
  refine ⟨18341444676536622170845673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195642076549723969822353845 18341444676536622170845673)
  ·
    refine ⟨13756083507402466628134255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18341444676536622170845673 13756083507402466628134255)
    ·
      refine ⟨20634125261103699942201383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13756083507402466628134255 20634125261103699942201383)
      ·
        refine ⟨30951187891655549913302075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20634125261103699942201383 30951187891655549913302075)
        ·
          refine ⟨46426781837483324869953113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30951187891655549913302075 46426781837483324869953113)
          ·
            refine ⟨34820086378112493652464835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46426781837483324869953113 34820086378112493652464835)
            ·
              refine ⟨52230129567168740478697253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34820086378112493652464835 52230129567168740478697253)
              ·
                refine ⟨9793149293844138839755735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52230129567168740478697253 9793149293844138839755735)
                ·
                  refine ⟨14689723940766208259633603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9793149293844138839755735 14689723940766208259633603)
                  ·
                    refine ⟨22034585911149312389450405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14689723940766208259633603 22034585911149312389450405)
                    ·
                      refine ⟨4131484858340496073021951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22034585911149312389450405 4131484858340496073021951)
                      ·
                        rfl

theorem cell23_8046038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_8046038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046038 prefixEnd_8046038 := by exact prefixLift 8046038
  have htrace : WordTrace (prefixWord ++ tailWord_8046038) baseStart_8046038 baseEnd_8046038 := by
    simpa [prefixWord, tailWord_8046038, baseEnd_8046038] using wordTrace_append hprefix tailTrace_8046038
  have hstable : (prefixWord ++ tailWord_8046038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046038).length < 2 ^ (prefixWord ++ tailWord_8046038).sum := by decide
  have hdescent : baseEnd_8046038 < baseStart_8046038 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046041 : List Nat := [1, 2, 1, 2, 4, 2, 1, 4, 1, 2, 3]
def baseStart_8046041 : Nat := 118140960795 + 8046041 * 2 ^ 59
def prefixEnd_8046041 : Nat := 4983230072969 + 3 ^ 40 * 8046041 * 2
def baseEnd_8046041 : Nat := 4131486398782459561284437

theorem tailTrace_8046041 : CollatzResearch.WordTrace tailWord_8046041 prefixEnd_8046041 4131486398782459561284437 := by
  unfold tailWord_8046041
  simp only [CollatzResearch.WordTrace]
  refine ⟨293463224243575086245889977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195642149495716724163926651 293463224243575086245889977)
  ·
    refine ⟨220097418182681314684417483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293463224243575086245889977 220097418182681314684417483)
    ·
      refine ⟨330146127274021972026626225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220097418182681314684417483 330146127274021972026626225)
      ·
        refine ⟨247609595455516479019969669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330146127274021972026626225 247609595455516479019969669)
        ·
          refine ⟨46426799147909339816244313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 247609595455516479019969669 46426799147909339816244313)
          ·
            refine ⟨34820099360932004862183235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46426799147909339816244313 34820099360932004862183235)
            ·
              refine ⟨52230149041398007293274853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34820099360932004862183235 52230149041398007293274853)
              ·
                refine ⟨9793152945262126367489035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52230149041398007293274853 9793152945262126367489035)
                ·
                  refine ⟨14689729417893189551233553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9793152945262126367489035 14689729417893189551233553)
                  ·
                    refine ⟨11017297063419892163425165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14689729417893189551233553 11017297063419892163425165)
                    ·
                      refine ⟨4131486398782459561284437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11017297063419892163425165 4131486398782459561284437)
                      ·
                        rfl

theorem cell23_8046041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 4, 1, 2, 3].length) (baseStart_8046041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046041 prefixEnd_8046041 := by exact prefixLift 8046041
  have htrace : WordTrace (prefixWord ++ tailWord_8046041) baseStart_8046041 baseEnd_8046041 := by
    simpa [prefixWord, tailWord_8046041, baseEnd_8046041] using wordTrace_append hprefix tailTrace_8046041
  have hstable : (prefixWord ++ tailWord_8046041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046041).length < 2 ^ (prefixWord ++ tailWord_8046041).sum := by decide
  have hdescent : baseEnd_8046041 < baseStart_8046041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046061 : List Nat := [1, 5, 1, 3, 2, 2, 9]
def baseStart_8046061 : Nat := 118140960795 + 8046061 * 2 ^ 59
def prefixEnd_8046061 : Nat := 4983230072969 + 3 ^ 40 * 8046061 * 2
def baseEnd_8046061 : Nat := 51006131708587030654745

theorem tailTrace_8046061 : CollatzResearch.WordTrace tailWord_8046061 prefixEnd_8046061 51006131708587030654745 := by
  unfold tailWord_8046061
  simp only [CollatzResearch.WordTrace]
  refine ⟨293463953703502629661618037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195642635802335086441078691 293463953703502629661618037)
  ·
    refine ⟨27512245659703371530776691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293463953703502629661618037 27512245659703371530776691)
    ·
      refine ⟨41268368489555057296165037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27512245659703371530776691 41268368489555057296165037)
      ·
        refine ⟨15475638183583146486061889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 41268368489555057296165037 15475638183583146486061889)
        ·
          refine ⟨11606728637687359864546417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15475638183583146486061889 11606728637687359864546417)
          ·
            refine ⟨8705046478265519898409813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11606728637687359864546417 8705046478265519898409813)
            ·
              refine ⟨51006131708587030654745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8705046478265519898409813 51006131708587030654745)
              ·
                rfl

theorem cell23_8046061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 2, 9].length) (baseStart_8046061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046061 prefixEnd_8046061 := by exact prefixLift 8046061
  have htrace : WordTrace (prefixWord ++ tailWord_8046061) baseStart_8046061 baseEnd_8046061 := by
    simpa [prefixWord, tailWord_8046061, baseEnd_8046061] using wordTrace_append hprefix tailTrace_8046061
  have hstable : (prefixWord ++ tailWord_8046061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046061).length < 2 ^ (prefixWord ++ tailWord_8046061).sum := by decide
  have hdescent : baseEnd_8046061 < baseStart_8046061 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046072 : List Nat := [2, 1, 2, 1, 1, 6, 3, 2, 1, 2, 2]
def baseStart_8046072 : Nat := 118140960795 + 8046072 * 2 ^ 59
def prefixEnd_8046072 : Nat := 4983230072969 + 3 ^ 40 * 8046072 * 2
def baseEnd_8046072 : Nat := 4131502316682748939996795

theorem tailTrace_8046072 : CollatzResearch.WordTrace tailWord_8046072 prefixEnd_8046072 4131502316682748939996795 := by
  unfold tailWord_8046072
  simp only [CollatzResearch.WordTrace]
  refine ⟨146732177453231389270134235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195642903270975185693512313 146732177453231389270134235)
  ·
    refine ⟨220098266179847083905201353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146732177453231389270134235 220098266179847083905201353)
    ·
      refine ⟨165073699634885312928901015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220098266179847083905201353 165073699634885312928901015)
      ·
        refine ⟨247610549452327969393351523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165073699634885312928901015 247610549452327969393351523)
        ·
          refine ⟨371415824178491954090027285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247610549452327969393351523 371415824178491954090027285)
          ·
            refine ⟨17410116758366810347970029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 371415824178491954090027285 17410116758366810347970029)
            ·
              refine ⟨6528793784387553880488761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17410116758366810347970029 6528793784387553880488761)
              ·
                refine ⟨4896595338290665410366571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6528793784387553880488761 4896595338290665410366571)
                ·
                  refine ⟨7344893007435998115549857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896595338290665410366571 7344893007435998115549857)
                  ·
                    refine ⟨5508669755576998586662393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7344893007435998115549857 5508669755576998586662393)
                    ·
                      refine ⟨4131502316682748939996795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508669755576998586662393 4131502316682748939996795)
                      ·
                        rfl

theorem cell23_8046072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 3, 2, 1, 2, 2].length) (baseStart_8046072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046072 prefixEnd_8046072 := by exact prefixLift 8046072
  have htrace : WordTrace (prefixWord ++ tailWord_8046072) baseStart_8046072 baseEnd_8046072 := by
    simpa [prefixWord, tailWord_8046072, baseEnd_8046072] using wordTrace_append hprefix tailTrace_8046072
  have hstable : (prefixWord ++ tailWord_8046072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046072).length < 2 ^ (prefixWord ++ tailWord_8046072).sum := by decide
  have hdescent : baseEnd_8046072 < baseStart_8046072 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046078 : List Nat := [4, 2, 2, 3, 1, 1, 2, 8]
def baseStart_8046078 : Nat := 118140960795 + 8046078 * 2 ^ 59
def prefixEnd_8046078 : Nat := 4983230072969 + 3 ^ 40 * 8046078 * 2
def baseEnd_8046078 : Nat := 153018718428395404315621

theorem tailTrace_8046078 : CollatzResearch.WordTrace tailWord_8046078 prefixEnd_8046078 153018718428395404315621 := by
  unfold tailWord_8046078
  simp only [CollatzResearch.WordTrace]
  refine ⟨36683071718055130195623361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195643049162960694376657925 36683071718055130195623361)
  ·
    refine ⟨27512303788541347646717521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36683071718055130195623361 27512303788541347646717521)
    ·
      refine ⟨20634227841406010735038141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27512303788541347646717521 20634227841406010735038141)
      ·
        refine ⟨7737835440527254025639303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20634227841406010735038141 7737835440527254025639303)
        ·
          refine ⟨11606753160790881038458955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7737835440527254025639303 11606753160790881038458955)
          ·
            refine ⟨17410129741186321557688433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11606753160790881038458955 17410129741186321557688433)
            ·
              refine ⟨13057597305889741168266325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17410129741186321557688433 13057597305889741168266325)
              ·
                refine ⟨153018718428395404315621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13057597305889741168266325 153018718428395404315621)
                ·
                  rfl

theorem cell23_8046078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_8046078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046078 prefixEnd_8046078 := by exact prefixLift 8046078
  have htrace : WordTrace (prefixWord ++ tailWord_8046078) baseStart_8046078 baseEnd_8046078 := by
    simpa [prefixWord, tailWord_8046078, baseEnd_8046078] using wordTrace_append hprefix tailTrace_8046078
  have hstable : (prefixWord ++ tailWord_8046078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046078).length < 2 ^ (prefixWord ++ tailWord_8046078).sum := by decide
  have hdescent : baseEnd_8046078 < baseStart_8046078 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046082 : List Nat := [3, 4, 1, 2, 1, 3, 2, 1, 2, 4]
def baseStart_8046082 : Nat := 118140960795 + 8046082 * 2 ^ 59
def prefixEnd_8046082 : Nat := 4983230072969 + 3 ^ 40 * 8046082 * 2
def baseEnd_8046082 : Nat := 1377169150496431300290583

theorem tailTrace_8046082 : CollatzResearch.WordTrace tailWord_8046082 prefixEnd_8046082 1377169150496431300290583 := by
  unfold tailWord_8046082
  simp only [CollatzResearch.WordTrace]
  refine ⟨73366179909106637562033125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195643146424284366832088333 73366179909106637562033125)
  ·
    refine ⟨13756158732957494542881211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 73366179909106637562033125 13756158732957494542881211)
    ·
      refine ⟨20634238099436241814321817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13756158732957494542881211 20634238099436241814321817)
      ·
        refine ⟨15475678574577181360741363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20634238099436241814321817 15475678574577181360741363)
        ·
          refine ⟨23213517861865772041112045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15475678574577181360741363 23213517861865772041112045)
          ·
            refine ⟨8705069198199664515417017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23213517861865772041112045 8705069198199664515417017)
            ·
              refine ⟨6528801898649748386562763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8705069198199664515417017 6528801898649748386562763)
              ·
                refine ⟨9793202847974622579844145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6528801898649748386562763 9793202847974622579844145)
                ·
                  refine ⟨7344902135980966934883109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9793202847974622579844145 7344902135980966934883109)
                  ·
                    refine ⟨1377169150496431300290583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7344902135980966934883109 1377169150496431300290583)
                    ·
                      rfl

theorem cell23_8046082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_8046082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046082 prefixEnd_8046082 := by exact prefixLift 8046082
  have htrace : WordTrace (prefixWord ++ tailWord_8046082) baseStart_8046082 baseEnd_8046082 := by
    simpa [prefixWord, tailWord_8046082, baseEnd_8046082] using wordTrace_append hprefix tailTrace_8046082
  have hstable : (prefixWord ++ tailWord_8046082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046082).length < 2 ^ (prefixWord ++ tailWord_8046082).sum := by decide
  have hdescent : baseEnd_8046082 < baseStart_8046082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046111 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 3, 4, 2]
def baseStart_8046111 : Nat := 118140960795 + 8046111 * 2 ^ 59
def prefixEnd_8046111 : Nat := 4983230072969 + 3 ^ 40 * 8046111 * 2
def baseEnd_8046111 : Nat := 4131522342428274287409115

theorem tailTrace_8046111 : CollatzResearch.WordTrace tailWord_8046111 prefixEnd_8046111 4131522342428274287409115 := by
  unfold tailWord_8046111
  simp only [CollatzResearch.WordTrace]
  refine ⟨293465777353321488200938187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195643851568880992133958791 293465777353321488200938187)
  ·
    refine ⟨440198666029982232301407281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293465777353321488200938187 440198666029982232301407281)
    ·
      refine ⟨330148999522486674226055461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440198666029982232301407281 330148999522486674226055461)
      ·
        refine ⟨61902937410466251417385399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330148999522486674226055461 61902937410466251417385399)
        ·
          refine ⟨92854406115699377126078099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61902937410466251417385399 92854406115699377126078099)
          ·
            refine ⟨139281609173549065689117149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92854406115699377126078099 139281609173549065689117149)
            ·
              refine ⟨52230603440080899633418931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139281609173549065689117149 52230603440080899633418931)
              ·
                refine ⟨78345905160121349450128397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52230603440080899633418931 78345905160121349450128397)
                ·
                  refine ⟨29379714435045506043798149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78345905160121349450128397 29379714435045506043798149)
                  ·
                    refine ⟨5508696456571032383212153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29379714435045506043798149 5508696456571032383212153)
                    ·
                      refine ⟨4131522342428274287409115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508696456571032383212153 4131522342428274287409115)
                      ·
                        rfl

theorem cell23_8046111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 4, 2].length) (baseStart_8046111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046111 prefixEnd_8046111 := by exact prefixLift 8046111
  have htrace : WordTrace (prefixWord ++ tailWord_8046111) baseStart_8046111 baseEnd_8046111 := by
    simpa [prefixWord, tailWord_8046111, baseEnd_8046111] using wordTrace_append hprefix tailTrace_8046111
  have hstable : (prefixWord ++ tailWord_8046111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046111).length < 2 ^ (prefixWord ++ tailWord_8046111).sum := by decide
  have hdescent : baseEnd_8046111 < baseStart_8046111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046145 : List Nat := [1, 2, 5, 1, 1, 1, 1, 5, 2, 2, 2]
def baseStart_8046145 : Nat := 118140960795 + 8046145 * 2 ^ 59
def prefixEnd_8046145 : Nat := 4983230072969 + 3 ^ 40 * 8046145 * 2
def baseEnd_8046145 : Nat := 4131539800770527154383959

theorem tailTrace_8046145 : CollatzResearch.WordTrace tailWord_8046145 prefixEnd_8046145 4131539800770527154383959 := by
  unfold tailWord_8046145
  simp only [CollatzResearch.WordTrace]
  refine ⟨293467017435198312007675889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195644678290132208005117259 293467017435198312007675889)
  ·
    refine ⟨220100263076398734005756917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293467017435198312007675889 220100263076398734005756917)
    ·
      refine ⟨20634399663412381313039711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 220100263076398734005756917 20634399663412381313039711)
      ·
        refine ⟨30951599495118571969559567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20634399663412381313039711 30951599495118571969559567)
        ·
          refine ⟨46427399242677857954339351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30951599495118571969559567 46427399242677857954339351)
          ·
            refine ⟨69641098864016786931509027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46427399242677857954339351 69641098864016786931509027)
            ·
              refine ⟨104461648296025180397263541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69641098864016786931509027 104461648296025180397263541)
              ·
                refine ⟨9793279527752360662243457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104461648296025180397263541 9793279527752360662243457)
                ·
                  refine ⟨7344959645814270496682593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9793279527752360662243457 7344959645814270496682593)
                  ·
                    refine ⟨5508719734360702872511945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7344959645814270496682593 5508719734360702872511945)
                    ·
                      refine ⟨4131539800770527154383959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508719734360702872511945 4131539800770527154383959)
                      ·
                        rfl

theorem cell23_8046145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 2, 2].length) (baseStart_8046145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046145 prefixEnd_8046145 := by exact prefixLift 8046145
  have htrace : WordTrace (prefixWord ++ tailWord_8046145) baseStart_8046145 baseEnd_8046145 := by
    simpa [prefixWord, tailWord_8046145, baseEnd_8046145] using wordTrace_append hprefix tailTrace_8046145
  have hstable : (prefixWord ++ tailWord_8046145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046145).length < 2 ^ (prefixWord ++ tailWord_8046145).sum := by decide
  have hdescent : baseEnd_8046145 < baseStart_8046145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046151 : List Nat := [1, 1, 4, 1, 5, 1, 1, 2, 7]
def baseStart_8046151 : Nat := 118140960795 + 8046151 * 2 ^ 59
def prefixEnd_8046151 : Nat := 4983230072969 + 3 ^ 40 * 8046151 * 2
def baseEnd_8046151 : Nat := 459060320183828236767659

theorem tailTrace_8046151 : CollatzResearch.WordTrace tailWord_8046151 prefixEnd_8046151 459060320183828236767659 := by
  unfold tailWord_8046151
  simp only [CollatzResearch.WordTrace]
  refine ⟨293467236273176575032394307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195644824182117716688262871 293467236273176575032394307)
  ·
    refine ⟨440200854409764862548591461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293467236273176575032394307 440200854409764862548591461)
    ·
      refine ⟨82537660201830911727860899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440200854409764862548591461 82537660201830911727860899)
      ·
        refine ⟨123806490302746367591791349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82537660201830911727860899 123806490302746367591791349)
        ·
          refine ⟨11606858465882471961730439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 123806490302746367591791349 11606858465882471961730439)
          ·
            refine ⟨17410287698823707942595659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11606858465882471961730439 17410287698823707942595659)
            ·
              refine ⟨26115431548235561913893489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17410287698823707942595659 26115431548235561913893489)
              ·
                refine ⟨19586573661176671435420117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26115431548235561913893489 19586573661176671435420117)
                ·
                  refine ⟨459060320183828236767659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19586573661176671435420117 459060320183828236767659)
                  ·
                    rfl

theorem cell23_8046151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 2, 7].length) (baseStart_8046151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046151 prefixEnd_8046151 := by exact prefixLift 8046151
  have htrace : WordTrace (prefixWord ++ tailWord_8046151) baseStart_8046151 baseEnd_8046151 := by
    simpa [prefixWord, tailWord_8046151, baseEnd_8046151] using wordTrace_append hprefix tailTrace_8046151
  have hstable : (prefixWord ++ tailWord_8046151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046151).length < 2 ^ (prefixWord ++ tailWord_8046151).sum := by decide
  have hdescent : baseEnd_8046151 < baseStart_8046151 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046241 : List Nat := [1, 2, 3, 3, 2, 1, 2, 1, 8]
def baseStart_8046241 : Nat := 118140960795 + 8046241 * 2 ^ 59
def prefixEnd_8046241 : Nat := 4983230072969 + 3 ^ 40 * 8046241 * 2
def baseEnd_8046241 : Nat := 459065454990373197642613

theorem tailTrace_8046241 : CollatzResearch.WordTrace tailWord_8046241 prefixEnd_8046241 459065454990373197642613 := by
  unfold tailWord_8046241
  simp only [CollatzResearch.WordTrace]
  refine ⟨293470518842850520403170577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195647012561900346935447051 293470518842850520403170577)
  ·
    refine ⟨220102889132137890302377933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293470518842850520403170577 220102889132137890302377933)
    ·
      refine ⟨82538583424551708863391725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220102889132137890302377933 82538583424551708863391725)
      ·
        refine ⟨30951968784206890823771897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82538583424551708863391725 30951968784206890823771897)
        ·
          refine ⟨23213976588155168117828923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30951968784206890823771897 23213976588155168117828923)
          ·
            refine ⟨34820964882232752176743385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23213976588155168117828923 34820964882232752176743385)
            ·
              refine ⟨26115723661674564132557539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34820964882232752176743385 26115723661674564132557539)
              ·
                refine ⟨39173585492511846198836309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26115723661674564132557539 39173585492511846198836309)
                ·
                  refine ⟨459065454990373197642613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39173585492511846198836309 459065454990373197642613)
                  ·
                    rfl

theorem cell23_8046241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 2, 1, 8].length) (baseStart_8046241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046241 prefixEnd_8046241 := by exact prefixLift 8046241
  have htrace : WordTrace (prefixWord ++ tailWord_8046241) baseStart_8046241 baseEnd_8046241 := by
    simpa [prefixWord, tailWord_8046241, baseEnd_8046241] using wordTrace_append hprefix tailTrace_8046241
  have hstable : (prefixWord ++ tailWord_8046241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046241).length < 2 ^ (prefixWord ++ tailWord_8046241).sum := by decide
  have hdescent : baseEnd_8046241 < baseStart_8046241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046258 : List Nat := [3, 2, 1, 1, 1, 2, 6, 1, 6]
def baseStart_8046258 : Nat := 118140960795 + 8046258 * 2 ^ 59
def prefixEnd_8046258 : Nat := 4983230072969 + 3 ^ 40 * 8046258 * 2
def baseEnd_8046258 : Nat := 459066424898276134696771

theorem tailTrace_8046258 : CollatzResearch.WordTrace tailWord_8046258 prefixEnd_8046258 459066424898276134696771 := by
  unfold tailWord_8046258
  simp only [CollatzResearch.WordTrace]
  refine ⟨73367784720947233076634857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195647425922525954871026285 73367784720947233076634857)
  ·
    refine ⟨55025838540710424807476143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73367784720947233076634857 55025838540710424807476143)
    ·
      refine ⟨82538757811065637211214215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55025838540710424807476143 82538757811065637211214215)
      ·
        refine ⟨123808136716598455816821323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82538757811065637211214215 123808136716598455816821323)
        ·
          refine ⟨185712205074897683725231985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123808136716598455816821323 185712205074897683725231985)
          ·
            refine ⟨139284153806173262793923989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185712205074897683725231985 139284153806173262793923989)
            ·
              refine ⟨6528944709664371693465187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 139284153806173262793923989 6528944709664371693465187)
              ·
                refine ⟨9793417064496557540197781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6528944709664371693465187 9793417064496557540197781)
                ·
                  refine ⟨459066424898276134696771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9793417064496557540197781 459066424898276134696771)
                  ·
                    rfl

theorem cell23_8046258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 6, 1, 6].length) (baseStart_8046258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046258 prefixEnd_8046258 := by exact prefixLift 8046258
  have htrace : WordTrace (prefixWord ++ tailWord_8046258) baseStart_8046258 baseEnd_8046258 := by
    simpa [prefixWord, tailWord_8046258, baseEnd_8046258] using wordTrace_append hprefix tailTrace_8046258
  have hstable : (prefixWord ++ tailWord_8046258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046258).length < 2 ^ (prefixWord ++ tailWord_8046258).sum := by decide
  have hdescent : baseEnd_8046258 < baseStart_8046258 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046271 : List Nat := [1, 1, 2, 2, 2, 3, 3, 1, 3, 5]
def baseStart_8046271 : Nat := 118140960795 + 8046271 * 2 ^ 59
def prefixEnd_8046271 : Nat := 4983230072969 + 3 ^ 40 * 8046271 * 2
def baseEnd_8046271 : Nat := 1377201499777664553802793

theorem tailTrace_8046271 : CollatzResearch.WordTrace tailWord_8046271 prefixEnd_8046271 1377201499777664553802793 := by
  unfold tailWord_8046271
  simp only [CollatzResearch.WordTrace]
  refine ⟨293471613032741835526762667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195647742021827890351175111 293471613032741835526762667)
  ·
    refine ⟨440207419549112753290144001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293471613032741835526762667 440207419549112753290144001)
    ·
      refine ⟨330155564661834564967608001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440207419549112753290144001 330155564661834564967608001)
      ·
        refine ⟨247616673496375923725706001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330155564661834564967608001 247616673496375923725706001)
        ·
          refine ⟨185712505122281942794279501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247616673496375923725706001 185712505122281942794279501)
          ·
            refine ⟨69642189420855728547854813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185712505122281942794279501 69642189420855728547854813)
            ·
              refine ⟨26115821032820898205445555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69642189420855728547854813 26115821032820898205445555)
              ·
                refine ⟨39173731549231347308168333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26115821032820898205445555 39173731549231347308168333)
                ·
                  refine ⟨14690149330961755240563125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39173731549231347308168333 14690149330961755240563125)
                  ·
                    refine ⟨1377201499777664553802793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14690149330961755240563125 1377201499777664553802793)
                    ·
                      rfl

theorem cell23_8046271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 1, 3, 5].length) (baseStart_8046271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046271 prefixEnd_8046271 := by exact prefixLift 8046271
  have htrace : WordTrace (prefixWord ++ tailWord_8046271) baseStart_8046271 baseEnd_8046271 := by
    simpa [prefixWord, tailWord_8046271, baseEnd_8046271] using wordTrace_append hprefix tailTrace_8046271
  have hstable : (prefixWord ++ tailWord_8046271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046271).length < 2 ^ (prefixWord ++ tailWord_8046271).sum := by decide
  have hdescent : baseEnd_8046271 < baseStart_8046271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046318 : List Nat := [4, 1, 2, 1, 1, 2, 4, 1, 1, 6]
def baseStart_8046318 : Nat := 118140960795 + 8046318 * 2 ^ 59
def prefixEnd_8046318 : Nat := 4983230072969 + 3 ^ 40 * 8046318 * 2
def baseEnd_8046318 : Nat := 1377209544307918325840221

theorem tailTrace_8046318 : CollatzResearch.WordTrace tailWord_8046318 prefixEnd_8046318 1377209544307918325840221 := by
  unfold tailWord_8046318
  simp only [CollatzResearch.WordTrace]
  refine ⟨36684165907946445319215451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195648884842381041702482405 36684165907946445319215451)
  ·
    refine ⟨55026248861919667978823177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36684165907946445319215451 55026248861919667978823177)
    ·
      refine ⟨41269686646439750984117383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55026248861919667978823177 41269686646439750984117383)
      ·
        refine ⟨61904529969659626476176075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41269686646439750984117383 61904529969659626476176075)
        ·
          refine ⟨92856794954489439714264113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61904529969659626476176075 92856794954489439714264113)
          ·
            refine ⟨69642596215867079785698085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92856794954489439714264113 69642596215867079785698085)
            ·
              refine ⟨13057986790475077459818391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69642596215867079785698085 13057986790475077459818391)
              ·
                refine ⟨19586980185712616189727587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13057986790475077459818391 19586980185712616189727587)
                ·
                  refine ⟨29380470278568924284591381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19586980185712616189727587 29380470278568924284591381)
                  ·
                    refine ⟨1377209544307918325840221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29380470278568924284591381 1377209544307918325840221)
                    ·
                      rfl

theorem cell23_8046318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 1, 1, 6].length) (baseStart_8046318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046318 prefixEnd_8046318 := by exact prefixLift 8046318
  have htrace : WordTrace (prefixWord ++ tailWord_8046318) baseStart_8046318 baseEnd_8046318 := by
    simpa [prefixWord, tailWord_8046318, baseEnd_8046318] using wordTrace_append hprefix tailTrace_8046318
  have hstable : (prefixWord ++ tailWord_8046318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046318).length < 2 ^ (prefixWord ++ tailWord_8046318).sum := by decide
  have hdescent : baseEnd_8046318 < baseStart_8046318 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046359 : List Nat := [1, 1, 3, 4, 2, 1, 2, 4, 1, 2, 2]
def baseStart_8046359 : Nat := 118140960795 + 8046359 * 2 ^ 59
def prefixEnd_8046359 : Nat := 4983230072969 + 3 ^ 40 * 8046359 * 2
def baseEnd_8046359 : Nat := 4131649685630589317107975

theorem tailTrace_8046359 : CollatzResearch.WordTrace tailWord_8046359 prefixEnd_8046359 4131649685630589317107975 := by
  unfold tailWord_8046359
  simp only [CollatzResearch.WordTrace]
  refine ⟨293474822656423026555966131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195649881770948684370644087 293474822656423026555966131)
  ·
    refine ⟨440212233984634539833949197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293474822656423026555966131 440212233984634539833949197)
    ·
      refine ⟨165079587744237952437730949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440212233984634539833949197 165079587744237952437730949)
      ·
        refine ⟨30952422702044616082074553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 165079587744237952437730949 30952422702044616082074553)
        ·
          refine ⟨23214317026533462061555915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30952422702044616082074553 23214317026533462061555915)
          ·
            refine ⟨34821475539800193092333873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23214317026533462061555915 34821475539800193092333873)
            ·
              refine ⟨26116106654850144819250405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34821475539800193092333873 26116106654850144819250405)
              ·
                refine ⟨4896769997784402153609451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26116106654850144819250405 4896769997784402153609451)
                ·
                  refine ⟨7345154996676603230414177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896769997784402153609451 7345154996676603230414177)
                  ·
                    refine ⟨5508866247507452422810633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7345154996676603230414177 5508866247507452422810633)
                    ·
                      refine ⟨4131649685630589317107975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508866247507452422810633 4131649685630589317107975)
                      ·
                        rfl

theorem cell23_8046359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_8046359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046359 prefixEnd_8046359 := by exact prefixLift 8046359
  have htrace : WordTrace (prefixWord ++ tailWord_8046359) baseStart_8046359 baseEnd_8046359 := by
    simpa [prefixWord, tailWord_8046359, baseEnd_8046359] using wordTrace_append hprefix tailTrace_8046359
  have hstable : (prefixWord ++ tailWord_8046359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046359).length < 2 ^ (prefixWord ++ tailWord_8046359).sum := by decide
  have hdescent : baseEnd_8046359 < baseStart_8046359 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046382 : List Nat := [4, 1, 3, 2, 2, 2, 2, 7]
def baseStart_8046382 : Nat := 118140960795 + 8046382 * 2 ^ 59
def prefixEnd_8046382 : Nat := 4983230072969 + 3 ^ 40 * 8046382 * 2
def baseEnd_8046382 : Nat := 153024499840208989893347

theorem tailTrace_8046382 : CollatzResearch.WordTrace tailWord_8046382 prefixEnd_8046382 153024499840208989893347 := by
  unfold tailWord_8046382
  simp only [CollatzResearch.WordTrace]
  refine ⟨36684457691917462685506675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195650441023559800989368933 36684457691917462685506675)
  ·
    refine ⟨55026686537876194028260013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36684457691917462685506675 55026686537876194028260013)
    ·
      refine ⟨20635007451703572760597505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55026686537876194028260013 20635007451703572760597505)
      ·
        refine ⟨15476255588777679570448129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20635007451703572760597505 15476255588777679570448129)
        ·
          refine ⟨11607191691583259677836097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15476255588777679570448129 11607191691583259677836097)
          ·
            refine ⟨8705393768687444758377073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11607191691583259677836097 8705393768687444758377073)
            ·
              refine ⟨6529045326515583568782805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8705393768687444758377073 6529045326515583568782805)
              ·
                refine ⟨153024499840208989893347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6529045326515583568782805 153024499840208989893347)
                ·
                  rfl

theorem cell23_8046382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_8046382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046382 prefixEnd_8046382 := by exact prefixLift 8046382
  have htrace : WordTrace (prefixWord ++ tailWord_8046382) baseStart_8046382 baseEnd_8046382 := by
    simpa [prefixWord, tailWord_8046382, baseEnd_8046382] using wordTrace_append hprefix tailTrace_8046382
  have hstable : (prefixWord ++ tailWord_8046382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046382).length < 2 ^ (prefixWord ++ tailWord_8046382).sum := by decide
  have hdescent : baseEnd_8046382 < baseStart_8046382 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046391 : List Nat := [1, 1, 3, 1, 2, 1, 2, 2, 4, 6]
def baseStart_8046391 : Nat := 118140960795 + 8046391 * 2 ^ 59
def prefixEnd_8046391 : Nat := 4983230072969 + 3 ^ 40 * 8046391 * 2
def baseEnd_8046391 : Nat := 1377222039003844397302609

theorem tailTrace_8046391 : CollatzResearch.WordTrace tailWord_8046391 prefixEnd_8046391 1377222039003844397302609 := by
  unfold tailWord_8046391
  simp only [CollatzResearch.WordTrace]
  refine ⟨293475989792307096021131027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195650659861538064014087351 293475989792307096021131027)
  ·
    refine ⟨440213984688460644031696541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293475989792307096021131027 440213984688460644031696541)
    ·
      refine ⟨165080244258172741511886203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440213984688460644031696541 165080244258172741511886203)
      ·
        refine ⟨247620366387259112267829305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165080244258172741511886203 247620366387259112267829305)
        ·
          refine ⟨185715274790444334200871979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247620366387259112267829305 185715274790444334200871979)
          ·
            refine ⟨278572912185666501301307969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185715274790444334200871979 278572912185666501301307969)
            ·
              refine ⟨208929684139249875975980977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278572912185666501301307969 208929684139249875975980977)
              ·
                refine ⟨156697263104437406981985733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208929684139249875975980977 156697263104437406981985733)
                ·
                  refine ⟨29380736832082013809122325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156697263104437406981985733 29380736832082013809122325)
                  ·
                    refine ⟨1377222039003844397302609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29380736832082013809122325 1377222039003844397302609)
                    ·
                      rfl

theorem cell23_8046391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 4, 6].length) (baseStart_8046391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046391 prefixEnd_8046391 := by exact prefixLift 8046391
  have htrace : WordTrace (prefixWord ++ tailWord_8046391) baseStart_8046391 baseEnd_8046391 := by
    simpa [prefixWord, tailWord_8046391, baseEnd_8046391] using wordTrace_append hprefix tailTrace_8046391
  have hstable : (prefixWord ++ tailWord_8046391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046391).length < 2 ^ (prefixWord ++ tailWord_8046391).sum := by decide
  have hdescent : baseEnd_8046391 < baseStart_8046391 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046393 : List Nat := [1, 2, 1, 7, 1, 2, 1, 3, 1, 2, 2]
def baseStart_8046393 : Nat := 118140960795 + 8046393 * 2 ^ 59
def prefixEnd_8046393 : Nat := 4983230072969 + 3 ^ 40 * 8046393 * 2
def baseEnd_8046393 : Nat := 4131667143972842184082819

theorem tailTrace_8046393 : CollatzResearch.WordTrace tailWord_8046393 prefixEnd_8046393 4131667143972842184082819 := by
  unfold tailWord_8046393
  simp only [CollatzResearch.WordTrace]
  refine ⟨293476062738299850362703833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195650708492199900241802555 293476062738299850362703833)
  ·
    refine ⟨220107047053724887772027875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293476062738299850362703833 220107047053724887772027875)
    ·
      refine ⟨330160570580587331658041813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220107047053724887772027875 330160570580587331658041813)
      ·
        refine ⟨7738138372982515585735355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 330160570580587331658041813 7738138372982515585735355)
        ·
          refine ⟨11607207559473773378603033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7738138372982515585735355 11607207559473773378603033)
          ·
            refine ⟨8705405669605330033952275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11607207559473773378603033 8705405669605330033952275)
            ·
              refine ⟨13058108504407995050928413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8705405669605330033952275 13058108504407995050928413)
              ·
                refine ⟨4896790689152998144098155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13058108504407995050928413 4896790689152998144098155)
                ·
                  refine ⟨7345186033729497216147233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896790689152998144098155 7345186033729497216147233)
                  ·
                    refine ⟨5508889525297122912110425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7345186033729497216147233 5508889525297122912110425)
                    ·
                      refine ⟨4131667143972842184082819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508889525297122912110425 4131667143972842184082819)
                      ·
                        rfl

theorem cell23_8046393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_8046393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046393 prefixEnd_8046393 := by exact prefixLift 8046393
  have htrace : WordTrace (prefixWord ++ tailWord_8046393) baseStart_8046393 baseEnd_8046393 := by
    simpa [prefixWord, tailWord_8046393, baseEnd_8046393] using wordTrace_append hprefix tailTrace_8046393
  have hstable : (prefixWord ++ tailWord_8046393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046393).length < 2 ^ (prefixWord ++ tailWord_8046393).sum := by decide
  have hdescent : baseEnd_8046393 < baseStart_8046393 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046436 : List Nat := [2, 3, 1, 1, 6, 1, 1, 2, 1, 3, 2]
def baseStart_8046436 : Nat := 118140960795 + 8046436 * 2 ^ 59
def prefixEnd_8046436 : Nat := 4983230072969 + 3 ^ 40 * 8046436 * 2
def baseEnd_8046436 : Nat := 4131689223640985515845121

theorem tailTrace_8046436 : CollatzResearch.WordTrace tailWord_8046436 prefixEnd_8046436 4131689223640985515845121 := by
  unfold tailWord_8046436
  simp only [CollatzResearch.WordTrace]
  refine ⟨146738815538572034353259581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195651754051429379137679441 146738815538572034353259581)
  ·
    refine ⟨55027055826964512882472343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146738815538572034353259581 55027055826964512882472343)
    ·
      refine ⟨82540583740446769323708515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55027055826964512882472343 82540583740446769323708515)
      ·
        refine ⟨123810875610670153985562773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82540583740446769323708515 123810875610670153985562773)
        ·
          refine ⟨5803634794250163468073255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 123810875610670153985562773 5803634794250163468073255)
          ·
            refine ⟨8705452191375245202109883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5803634794250163468073255 8705452191375245202109883)
            ·
              refine ⟨13058178287062867803164825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8705452191375245202109883 13058178287062867803164825)
              ·
                refine ⟨9793633715297150852373619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13058178287062867803164825 9793633715297150852373619)
                ·
                  refine ⟨14690450572945726278560429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9793633715297150852373619 14690450572945726278560429)
                  ·
                    refine ⟨5508918964854647354460161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14690450572945726278560429 5508918964854647354460161)
                    ·
                      refine ⟨4131689223640985515845121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5508918964854647354460161 4131689223640985515845121)
                      ·
                        rfl

theorem cell23_8046436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_8046436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046436 prefixEnd_8046436 := by exact prefixLift 8046436
  have htrace : WordTrace (prefixWord ++ tailWord_8046436) baseStart_8046436 baseEnd_8046436 := by
    simpa [prefixWord, tailWord_8046436, baseEnd_8046436] using wordTrace_append hprefix tailTrace_8046436
  have hstable : (prefixWord ++ tailWord_8046436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046436).length < 2 ^ (prefixWord ++ tailWord_8046436).sum := by decide
  have hdescent : baseEnd_8046436 < baseStart_8046436 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046441 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 8]
def baseStart_8046441 : Nat := 118140960795 + 8046441 * 2 ^ 59
def prefixEnd_8046441 : Nat := 4983230072969 + 3 ^ 40 * 8046441 * 2
def baseEnd_8046441 : Nat := 4131691791044257996282597

theorem tailTrace_8046441 : CollatzResearch.WordTrace tailWord_8046441 prefixEnd_8046441 4131691791044257996282597 := by
  unfold tailWord_8046441
  simp only [CollatzResearch.WordTrace]
  refine ⟨293477813442125954560451177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195651875628083969706967451 293477813442125954560451177)
  ·
    refine ⟨220108360081594465920338383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293477813442125954560451177 220108360081594465920338383)
    ·
      refine ⟨330162540122391698880507575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220108360081594465920338383 330162540122391698880507575)
      ·
        refine ⟨495243810183587548320761363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330162540122391698880507575 495243810183587548320761363)
        ·
          refine ⟨742865715275381322481142045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495243810183587548320761363 742865715275381322481142045)
          ·
            refine ⟨278574643228267995930428267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 742865715275381322481142045 278574643228267995930428267)
            ·
              refine ⟨417861964842401993895642401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278574643228267995930428267 417861964842401993895642401)
              ·
                refine ⟨313396473631801495421731801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417861964842401993895642401 313396473631801495421731801)
                ·
                  refine ⟨235047355223851121566298851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313396473631801495421731801 235047355223851121566298851)
                  ·
                    refine ⟨352571032835776682349448277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 235047355223851121566298851 352571032835776682349448277)
                    ·
                      refine ⟨4131691791044257996282597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 352571032835776682349448277 4131691791044257996282597)
                      ·
                        rfl

theorem cell23_8046441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 2, 1, 8].length) (baseStart_8046441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046441 prefixEnd_8046441 := by exact prefixLift 8046441
  have htrace : WordTrace (prefixWord ++ tailWord_8046441) baseStart_8046441 baseEnd_8046441 := by
    simpa [prefixWord, tailWord_8046441, baseEnd_8046441] using wordTrace_append hprefix tailTrace_8046441
  have hstable : (prefixWord ++ tailWord_8046441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046441).length < 2 ^ (prefixWord ++ tailWord_8046441).sum := by decide
  have hdescent : baseEnd_8046441 < baseStart_8046441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046448 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 3]
def baseStart_8046448 : Nat := 118140960795 + 8046448 * 2 ^ 59
def prefixEnd_8046448 : Nat := 4983230072969 + 3 ^ 40 * 8046448 * 2
def baseEnd_8046448 : Nat := 4131695385408839468895065

theorem tailTrace_8046448 : CollatzResearch.WordTrace tailWord_8046448 prefixEnd_8046448 4131695385408839468895065 := by
  unfold tailWord_8046448
  simp only [CollatzResearch.WordTrace]
  refine ⟨146739034376550297377977999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195652045835400396503970665 146739034376550297377977999)
  ·
    refine ⟨220108551564825446066966999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146739034376550297377977999 220108551564825446066966999)
    ·
      refine ⟨330162827347238169100450499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220108551564825446066966999 330162827347238169100450499)
      ·
        refine ⟨495244241020857253650675749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330162827347238169100450499 495244241020857253650675749)
        ·
          refine ⟨92858295191410735059501703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495244241020857253650675749 92858295191410735059501703)
          ·
            refine ⟨139287442787116102589252555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92858295191410735059501703 139287442787116102589252555)
            ·
              refine ⟨208931164180674153883878833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139287442787116102589252555 208931164180674153883878833)
              ·
                refine ⟨156698373135505615412909125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208931164180674153883878833 156698373135505615412909125)
                ·
                  refine ⟨29380944962907302889920461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156698373135505615412909125 29380944962907302889920461)
                  ·
                    refine ⟨11017854361090238583720173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29380944962907302889920461 11017854361090238583720173)
                    ·
                      refine ⟨4131695385408839468895065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11017854361090238583720173 4131695385408839468895065)
                      ·
                        rfl

theorem cell23_8046448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 3].length) (baseStart_8046448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046448 prefixEnd_8046448 := by exact prefixLift 8046448
  have htrace : WordTrace (prefixWord ++ tailWord_8046448) baseStart_8046448 baseEnd_8046448 := by
    simpa [prefixWord, tailWord_8046448, baseEnd_8046448] using wordTrace_append hprefix tailTrace_8046448
  have hstable : (prefixWord ++ tailWord_8046448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046448).length < 2 ^ (prefixWord ++ tailWord_8046448).sum := by decide
  have hdescent : baseEnd_8046448 < baseStart_8046448 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046472 : List Nat := [2, 1, 3, 3, 3, 1, 1, 4, 5]
def baseStart_8046472 : Nat := 118140960795 + 8046472 * 2 ^ 59
def prefixEnd_8046472 : Nat := 4983230072969 + 3 ^ 40 * 8046472 * 2
def baseEnd_8046472 : Nat := 459078634327171930554995

theorem tailTrace_8046472 : CollatzResearch.WordTrace tailWord_8046472 prefixEnd_8046472 459078634327171930554995 := by
  unfold tailWord_8046472
  simp only [CollatzResearch.WordTrace]
  refine ⟨146739472052506823427414835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195652629403342431236553113 146739472052506823427414835)
  ·
    refine ⟨220109208078760235141122253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146739472052506823427414835 220109208078760235141122253)
    ·
      refine ⟨82540953029535088177920845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 220109208078760235141122253 82540953029535088177920845)
      ·
        refine ⟨30952857386075658066720317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82540953029535088177920845 30952857386075658066720317)
        ·
          refine ⟨11607321519778371775020119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 30952857386075658066720317 11607321519778371775020119)
          ·
            refine ⟨17410982279667557662530179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11607321519778371775020119 17410982279667557662530179)
            ·
              refine ⟨26116473419501336493795269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17410982279667557662530179 26116473419501336493795269)
              ·
                refine ⟨4896838766156500592586613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26116473419501336493795269 4896838766156500592586613)
                ·
                  refine ⟨459078634327171930554995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4896838766156500592586613 459078634327171930554995)
                  ·
                    rfl

theorem cell23_8046472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 4, 5].length) (baseStart_8046472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046472 prefixEnd_8046472 := by exact prefixLift 8046472
  have htrace : WordTrace (prefixWord ++ tailWord_8046472) baseStart_8046472 baseEnd_8046472 := by
    simpa [prefixWord, tailWord_8046472, baseEnd_8046472] using wordTrace_append hprefix tailTrace_8046472
  have hstable : (prefixWord ++ tailWord_8046472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046472).length < 2 ^ (prefixWord ++ tailWord_8046472).sum := by decide
  have hdescent : baseEnd_8046472 < baseStart_8046472 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046482 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_8046482 : Nat := 118140960795 + 8046482 * 2 ^ 59
def prefixEnd_8046482 : Nat := 4983230072969 + 3 ^ 40 * 8046482 * 2
def baseEnd_8046482 : Nat := 4131712843751092335869909

theorem tailTrace_8046482 : CollatzResearch.WordTrace tailWord_8046482 prefixEnd_8046482 4131712843751092335869909 := by
  unfold tailWord_8046482
  simp only [CollatzResearch.WordTrace]
  refine ⟨73369827208744354640673425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195652872556651612375129133 73369827208744354640673425)
  ·
    refine ⟨55027370406558265980505069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73369827208744354640673425 55027370406558265980505069)
    ·
      refine ⟨20635263902459349742689401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 55027370406558265980505069 20635263902459349742689401)
      ·
        refine ⟨15476447926844512307017051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20635263902459349742689401 15476447926844512307017051)
        ·
          refine ⟨23214671890266768460525577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15476447926844512307017051 23214671890266768460525577)
          ·
            refine ⟨17411003917700076345394183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23214671890266768460525577 17411003917700076345394183)
            ·
              refine ⟨26116505876550114518091275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17411003917700076345394183 26116505876550114518091275)
              ·
                refine ⟨39174758814825171777136913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26116505876550114518091275 39174758814825171777136913)
                ·
                  refine ⟨29381069111118878832852685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39174758814825171777136913 29381069111118878832852685)
                  ·
                    refine ⟨11017900916669579562319757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29381069111118878832852685 11017900916669579562319757)
                    ·
                      refine ⟨4131712843751092335869909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11017900916669579562319757 4131712843751092335869909)
                      ·
                        rfl

theorem cell23_8046482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_8046482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046482 prefixEnd_8046482 := by exact prefixLift 8046482
  have htrace : WordTrace (prefixWord ++ tailWord_8046482) baseStart_8046482 baseEnd_8046482 := by
    simpa [prefixWord, tailWord_8046482, baseEnd_8046482] using wordTrace_append hprefix tailTrace_8046482
  have hstable : (prefixWord ++ tailWord_8046482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046482).length < 2 ^ (prefixWord ++ tailWord_8046482).sum := by decide
  have hdescent : baseEnd_8046482 < baseStart_8046482 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046528 : List Nat := [2, 1, 1, 2, 3, 2, 3, 1, 8]
def baseStart_8046528 : Nat := 118140960795 + 8046528 * 2 ^ 59
def prefixEnd_8046528 : Nat := 4983230072969 + 3 ^ 40 * 8046528 * 2
def baseEnd_8046528 : Nat := 459081829317911017321633

theorem tailTrace_8046528 : CollatzResearch.WordTrace tailWord_8046528 prefixEnd_8046528 459081829317911017321633 := by
  unfold tailWord_8046528
  simp only [CollatzResearch.WordTrace]
  refine ⟨146740493296405384209434119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195653991061873845612578825 146740493296405384209434119)
  ·
    refine ⟨220110739944608076314151179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146740493296405384209434119 220110739944608076314151179)
    ·
      refine ⟨330166109916912114471226769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220110739944608076314151179 330166109916912114471226769)
      ·
        refine ⟨247624582437684085853420077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330166109916912114471226769 247624582437684085853420077)
        ·
          refine ⟨92859218414131532195032529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247624582437684085853420077 92859218414131532195032529)
          ·
            refine ⟨69644413810598649146274397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92859218414131532195032529 69644413810598649146274397)
            ·
              refine ⟨26116655178974493429852899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69644413810598649146274397 26116655178974493429852899)
              ·
                refine ⟨39174982768461740144779349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26116655178974493429852899 39174982768461740144779349)
                ·
                  refine ⟨459081829317911017321633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39174982768461740144779349 459081829317911017321633)
                  ·
                    rfl

theorem cell23_8046528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 3, 1, 8].length) (baseStart_8046528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046528 prefixEnd_8046528 := by exact prefixLift 8046528
  have htrace : WordTrace (prefixWord ++ tailWord_8046528) baseStart_8046528 baseEnd_8046528 := by
    simpa [prefixWord, tailWord_8046528, baseEnd_8046528] using wordTrace_append hprefix tailTrace_8046528
  have hstable : (prefixWord ++ tailWord_8046528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046528).length < 2 ^ (prefixWord ++ tailWord_8046528).sum := by decide
  have hdescent : baseEnd_8046528 < baseStart_8046528 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046575 : List Nat := [1, 1, 2, 1, 4, 2, 1, 5, 1, 5]
def baseStart_8046575 : Nat := 118140960795 + 8046575 * 2 ^ 59
def prefixEnd_8046575 : Nat := 4983230072969 + 3 ^ 40 * 8046575 * 2
def baseEnd_8046575 : Nat := 1377253532483986824002327

theorem tailTrace_8046575 : CollatzResearch.WordTrace tailWord_8046575 prefixEnd_8046575 1377253532483986824002327 := by
  unfold tailWord_8046575
  simp only [CollatzResearch.WordTrace]
  refine ⟨293482700823640495445829179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195655133882426996963886119 293482700823640495445829179)
  ·
    refine ⟨440224051235460743168743769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293482700823640495445829179 440224051235460743168743769)
    ·
      refine ⟨330168038426595557376557827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440224051235460743168743769 330168038426595557376557827)
      ·
        refine ⟨495252057639893336064836741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330168038426595557376557827 495252057639893336064836741)
        ·
          refine ⟨92859760807480000512156889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495252057639893336064836741 92859760807480000512156889)
          ·
            refine ⟨69644820605610000384117667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92859760807480000512156889 69644820605610000384117667)
            ·
              refine ⟨104467230908415000576176501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69644820605610000384117667 104467230908415000576176501)
              ·
                refine ⟨9793802897663906304016547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104467230908415000576176501 9793802897663906304016547)
                ·
                  refine ⟨14690704346495859456024821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9793802897663906304016547 14690704346495859456024821)
                  ·
                    refine ⟨1377253532483986824002327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14690704346495859456024821 1377253532483986824002327)
                    ·
                      rfl

theorem cell23_8046575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 5, 1, 5].length) (baseStart_8046575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046575 prefixEnd_8046575 := by exact prefixLift 8046575
  have htrace : WordTrace (prefixWord ++ tailWord_8046575) baseStart_8046575 baseEnd_8046575 := by
    simpa [prefixWord, tailWord_8046575, baseEnd_8046575] using wordTrace_append hprefix tailTrace_8046575
  have hstable : (prefixWord ++ tailWord_8046575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046575).length < 2 ^ (prefixWord ++ tailWord_8046575).sum := by decide
  have hdescent : baseEnd_8046575 < baseStart_8046575 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046589 : List Nat := [1, 4, 1, 1, 1, 2, 2, 6, 1, 1, 3]
def baseStart_8046589 : Nat := 118140960795 + 8046589 * 2 ^ 59
def prefixEnd_8046589 : Nat := 4983230072969 + 3 ^ 40 * 8046589 * 2
def baseEnd_8046589 : Nat := 4131767786181123417231917

theorem tailTrace_8046589 : CollatzResearch.WordTrace tailWord_8046589 prefixEnd_8046589 4131767786181123417231917 := by
  unfold tailWord_8046589
  simp only [CollatzResearch.WordTrace]
  refine ⟨293483211445589775836838821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195655474297059850557892547 293483211445589775836838821)
  ·
    refine ⟨55028102146048082969407279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293483211445589775836838821 55028102146048082969407279)
    ·
      refine ⟨82542153219072124454110919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55028102146048082969407279 82542153219072124454110919)
      ·
        refine ⟨123813229828608186681166379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82542153219072124454110919 123813229828608186681166379)
        ·
          refine ⟨185719844742912280021749569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123813229828608186681166379 185719844742912280021749569)
          ·
            refine ⟨139289883557184210016312177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185719844742912280021749569 139289883557184210016312177)
            ·
              refine ⟨104467412667888157512234133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139289883557184210016312177 104467412667888157512234133)
              ·
                refine ⟨4896909968807257383385975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 104467412667888157512234133 4896909968807257383385975)
                ·
                  refine ⟨7345364953210886075078963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4896909968807257383385975 7345364953210886075078963)
                  ·
                    refine ⟨11018047429816329112618445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7345364953210886075078963 11018047429816329112618445)
                    ·
                      refine ⟨4131767786181123417231917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11018047429816329112618445 4131767786181123417231917)
                      ·
                        rfl

theorem cell23_8046589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 1, 1, 3].length) (baseStart_8046589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046589 prefixEnd_8046589 := by exact prefixLift 8046589
  have htrace : WordTrace (prefixWord ++ tailWord_8046589) baseStart_8046589 baseEnd_8046589 := by
    simpa [prefixWord, tailWord_8046589, baseEnd_8046589] using wordTrace_append hprefix tailTrace_8046589
  have hstable : (prefixWord ++ tailWord_8046589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046589).length < 2 ^ (prefixWord ++ tailWord_8046589).sum := by decide
  have hdescent : baseEnd_8046589 < baseStart_8046589 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046596 : List Nat := [2, 3, 2, 4, 1, 2, 2, 1, 6]
def baseStart_8046596 : Nat := 118140960795 + 8046596 * 2 ^ 59
def prefixEnd_8046596 : Nat := 4983230072969 + 3 ^ 40 * 8046596 * 2
def baseEnd_8046596 : Nat := 459085708949522765538265

theorem tailTrace_8046596 : CollatzResearch.WordTrace tailWord_8046596 prefixEnd_8046596 459085708949522765538265 := by
  unfold tailWord_8046596
  simp only [CollatzResearch.WordTrace]
  refine ⟨146741733378282208016171821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195655644504376277354895761 146741733378282208016171821)
  ·
    refine ⟨55028150016855828006064433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146741733378282208016171821 55028150016855828006064433)
    ·
      refine ⟨41271112512641871004548325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55028150016855828006064433 41271112512641871004548325)
      ·
        refine ⟨7738333596120350813352811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 41271112512641871004548325 7738333596120350813352811)
        ·
          refine ⟨11607500394180526220029217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7738333596120350813352811 11607500394180526220029217)
          ·
            refine ⟨8705625295635394665021913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11607500394180526220029217 8705625295635394665021913)
            ·
              refine ⟨6529218971726545998766435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8705625295635394665021913 6529218971726545998766435)
              ·
                refine ⟨9793828457589818998149653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6529218971726545998766435 9793828457589818998149653)
                ·
                  refine ⟨459085708949522765538265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9793828457589818998149653 459085708949522765538265)
                  ·
                    rfl

theorem cell23_8046596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_8046596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046596 prefixEnd_8046596 := by exact prefixLift 8046596
  have htrace : WordTrace (prefixWord ++ tailWord_8046596) baseStart_8046596 baseEnd_8046596 := by
    simpa [prefixWord, tailWord_8046596, baseEnd_8046596] using wordTrace_append hprefix tailTrace_8046596
  have hstable : (prefixWord ++ tailWord_8046596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046596).length < 2 ^ (prefixWord ++ tailWord_8046596).sum := by decide
  have hdescent : baseEnd_8046596 < baseStart_8046596 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046629 : List Nat := [1, 3, 1, 2, 2, 4, 3, 1, 1, 1, 4]
def baseStart_8046629 : Nat := 118140960795 + 8046629 * 2 ^ 59
def prefixEnd_8046629 : Nat := 4983230072969 + 3 ^ 40 * 8046629 * 2
def baseEnd_8046629 : Nat := 4131788325407303260731733

theorem tailTrace_8046629 : CollatzResearch.WordTrace tailWord_8046629 prefixEnd_8046629 4131788325407303260731733 := by
  unfold tailWord_8046629
  simp only [CollatzResearch.WordTrace]
  refine ⟨293484670365444862668294941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195656446910296575112196627 293484670365444862668294941)
  ·
    refine ⟨110056751387041823500610603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293484670365444862668294941 110056751387041823500610603)
    ·
      refine ⟨165085127080562735250915905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110056751387041823500610603 165085127080562735250915905)
      ·
        refine ⟨123813845310422051438186929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165085127080562735250915905 123813845310422051438186929)
        ·
          refine ⟨92860383982816538578640197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123813845310422051438186929 92860383982816538578640197)
          ·
            refine ⟨17411321996778100983495037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 92860383982816538578640197 17411321996778100983495037)
            ·
              refine ⟨6529245748791787868810639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17411321996778100983495037 6529245748791787868810639)
              ·
                refine ⟨9793868623187681803215959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6529245748791787868810639 9793868623187681803215959)
                ·
                  refine ⟨14690802934781522704823939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9793868623187681803215959 14690802934781522704823939)
                  ·
                    refine ⟨22036204402172284057235909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14690802934781522704823939 22036204402172284057235909)
                    ·
                      refine ⟨4131788325407303260731733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22036204402172284057235909 4131788325407303260731733)
                      ·
                        rfl

theorem cell23_8046629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 3, 1, 1, 1, 4].length) (baseStart_8046629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046629 prefixEnd_8046629 := by exact prefixLift 8046629
  have htrace : WordTrace (prefixWord ++ tailWord_8046629) baseStart_8046629 baseEnd_8046629 := by
    simpa [prefixWord, tailWord_8046629, baseEnd_8046629] using wordTrace_append hprefix tailTrace_8046629
  have hstable : (prefixWord ++ tailWord_8046629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046629).length < 2 ^ (prefixWord ++ tailWord_8046629).sum := by decide
  have hdescent : baseEnd_8046629 < baseStart_8046629 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046646 : List Nat := [5, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2]
def baseStart_8046646 : Nat := 118140960795 + 8046646 * 2 ^ 59
def prefixEnd_8046646 : Nat := 4983230072969 + 3 ^ 40 * 8046646 * 2
def baseEnd_8046646 : Nat := 4131797054578429694219155

theorem tailTrace_8046646 : CollatzResearch.WordTrace tailWord_8046646 prefixEnd_8046646 4131797054578429694219155 := by
  unfold tailWord_8046646
  simp only [CollatzResearch.WordTrace]
  refine ⟨18342830650398954660728987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195656860270922183047775861 18342830650398954660728987)
  ·
    refine ⟨27514245975598431991093481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18342830650398954660728987 27514245975598431991093481)
    ·
      refine ⟨20635684481698823993320111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27514245975598431991093481 20635684481698823993320111)
      ·
        refine ⟨30953526722548235989980167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20635684481698823993320111 30953526722548235989980167)
        ·
          refine ⟨46430290083822353984970251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30953526722548235989980167 46430290083822353984970251)
          ·
            refine ⟨69645435125733530977455377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46430290083822353984970251 69645435125733530977455377)
            ·
              refine ⟨52234076344300148233091533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69645435125733530977455377 52234076344300148233091533)
              ·
                refine ⟨19587778629112555587409325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52234076344300148233091533 19587778629112555587409325)
                ·
                  refine ⟨7345416985917208345278497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19587778629112555587409325 7345416985917208345278497)
                  ·
                    refine ⟨5509062739437906258958873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7345416985917208345278497 5509062739437906258958873)
                    ·
                      refine ⟨4131797054578429694219155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5509062739437906258958873 4131797054578429694219155)
                      ·
                        rfl

theorem cell23_8046646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_8046646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046646 prefixEnd_8046646 := by exact prefixLift 8046646
  have htrace : WordTrace (prefixWord ++ tailWord_8046646) baseStart_8046646 baseEnd_8046646 := by
    simpa [prefixWord, tailWord_8046646, baseEnd_8046646] using wordTrace_append hprefix tailTrace_8046646
  have hstable : (prefixWord ++ tailWord_8046646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046646).length < 2 ^ (prefixWord ++ tailWord_8046646).sum := by decide
  have hdescent : baseEnd_8046646 < baseStart_8046646 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046695 : List Nat := [1, 1, 5, 1, 1, 2, 1, 1, 4, 6]
def baseStart_8046695 : Nat := 118140960795 + 8046695 * 2 ^ 59
def prefixEnd_8046695 : Nat := 4983230072969 + 3 ^ 40 * 8046695 * 2
def baseEnd_8046695 : Nat := 1377274071710166667502143

theorem tailTrace_8046695 : CollatzResearch.WordTrace tailWord_8046695 prefixEnd_8046695 1377274071710166667502143 := by
  unfold tailWord_8046695
  simp only [CollatzResearch.WordTrace]
  refine ⟨293487077583205755940197539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195658051722137170626798359 293487077583205755940197539)
  ·
    refine ⟨440230616374808633910296309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293487077583205755940197539 440230616374808633910296309)
    ·
      refine ⟨41271620285138309429090279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 440230616374808633910296309 41271620285138309429090279)
      ·
        refine ⟨61907430427707464143635419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41271620285138309429090279 61907430427707464143635419)
        ·
          refine ⟨92861145641561196215453129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61907430427707464143635419 92861145641561196215453129)
          ·
            refine ⟨69645859231170897161589847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92861145641561196215453129 69645859231170897161589847)
            ·
              refine ⟨104468788846756345742384771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69645859231170897161589847 104468788846756345742384771)
              ·
                refine ⟨156703183270134518613577157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104468788846756345742384771 156703183270134518613577157)
                ·
                  refine ⟨29381846863150222240045717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156703183270134518613577157 29381846863150222240045717)
                  ·
                    refine ⟨1377274071710166667502143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29381846863150222240045717 1377274071710166667502143)
                    ·
                      rfl

theorem cell23_8046695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_8046695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046695 prefixEnd_8046695 := by exact prefixLift 8046695
  have htrace : WordTrace (prefixWord ++ tailWord_8046695) baseStart_8046695 baseEnd_8046695 := by
    simpa [prefixWord, tailWord_8046695, baseEnd_8046695] using wordTrace_append hprefix tailTrace_8046695
  have hstable : (prefixWord ++ tailWord_8046695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046695).length < 2 ^ (prefixWord ++ tailWord_8046695).sum := by decide
  have hdescent : baseEnd_8046695 < baseStart_8046695 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046806 : List Nat := [5, 2, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_8046806 : Nat := 118140960795 + 8046806 * 2 ^ 59
def prefixEnd_8046806 : Nat := 4983230072969 + 3 ^ 40 * 8046806 * 2
def baseEnd_8046806 : Nat := 1377293070494383022739473

theorem tailTrace_8046806 : CollatzResearch.WordTrace tailWord_8046806 prefixEnd_8046806 1377293070494383022739473 := by
  unfold tailWord_8046806
  simp only [CollatzResearch.WordTrace]
  refine ⟨18343195380362726368593017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195660750723869081264992181 18343195380362726368593017)
  ·
    refine ⟨13757396535272044776444763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18343195380362726368593017 13757396535272044776444763)
    ·
      refine ⟨20636094802908067164667145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13757396535272044776444763 20636094802908067164667145)
      ·
        refine ⟨15477071102181050373500359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20636094802908067164667145 15477071102181050373500359)
        ·
          refine ⟨23215606653271575560250539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15477071102181050373500359 23215606653271575560250539)
          ·
            refine ⟨34823409979907363340375809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23215606653271575560250539 34823409979907363340375809)
            ·
              refine ⟨26117557484930522505281857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34823409979907363340375809 26117557484930522505281857)
              ·
                refine ⟨19588168113697891878961393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26117557484930522505281857 19588168113697891878961393)
                ·
                  refine ⟨14691126085273418909221045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19588168113697891878961393 14691126085273418909221045)
                  ·
                    refine ⟨1377293070494383022739473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14691126085273418909221045 1377293070494383022739473)
                    ·
                      rfl

theorem cell23_8046806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_8046806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046806 prefixEnd_8046806 := by exact prefixLift 8046806
  have htrace : WordTrace (prefixWord ++ tailWord_8046806) baseStart_8046806 baseEnd_8046806 := by
    simpa [prefixWord, tailWord_8046806, baseEnd_8046806] using wordTrace_append hprefix tailTrace_8046806
  have hstable : (prefixWord ++ tailWord_8046806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046806).length < 2 ^ (prefixWord ++ tailWord_8046806).sum := by decide
  have hdescent : baseEnd_8046806 < baseStart_8046806 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046859 : List Nat := [1, 1, 1, 1, 5, 2, 1, 2, 5, 1, 3]
def baseStart_8046859 : Nat := 118140960795 + 8046859 * 2 ^ 59
def prefixEnd_8046859 : Nat := 4983230072969 + 3 ^ 40 * 8046859 * 2
def baseEnd_8046859 : Nat := 4131906425957837360855675

theorem tailTrace_8046859 : CollatzResearch.WordTrace tailWord_8046859 prefixEnd_8046859 4131906425957837360855675 := by
  unfold tailWord_8046859
  simp only [CollatzResearch.WordTrace]
  refine ⟨293493059154611611949167631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195662039436407741299445087 293493059154611611949167631)
  ·
    refine ⟨440239588731917417923751447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293493059154611611949167631 440239588731917417923751447)
    ·
      refine ⟨660359383097876126885627171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440239588731917417923751447 660359383097876126885627171)
      ·
        refine ⟨990539074646814190328440757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660359383097876126885627171 990539074646814190328440757)
        ·
          refine ⟨92863038248138830343291321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 990539074646814190328440757 92863038248138830343291321)
          ·
            refine ⟨69647278686104122757468491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92863038248138830343291321 69647278686104122757468491)
            ·
              refine ⟨104470918029156184136202737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69647278686104122757468491 104470918029156184136202737)
              ·
                refine ⟨78353188521867138102152053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104470918029156184136202737 78353188521867138102152053)
                ·
                  refine ⟨7345611423925044197076755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78353188521867138102152053 7345611423925044197076755)
                  ·
                    refine ⟨11018417135887566295615133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7345611423925044197076755 11018417135887566295615133)
                    ·
                      refine ⟨4131906425957837360855675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11018417135887566295615133 4131906425957837360855675)
                      ·
                        rfl

theorem cell23_8046859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 1, 3].length) (baseStart_8046859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046859 prefixEnd_8046859 := by exact prefixLift 8046859
  have htrace : WordTrace (prefixWord ++ tailWord_8046859) baseStart_8046859 baseEnd_8046859 := by
    simpa [prefixWord, tailWord_8046859, baseEnd_8046859] using wordTrace_append hprefix tailTrace_8046859
  have hstable : (prefixWord ++ tailWord_8046859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046859).length < 2 ^ (prefixWord ++ tailWord_8046859).sum := by decide
  have hdescent : baseEnd_8046859 < baseStart_8046859 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046899 : List Nat := [1, 1, 1, 2, 5, 1, 1, 1, 2, 6, 2]
def baseStart_8046899 : Nat := 118140960795 + 8046899 * 2 ^ 59
def prefixEnd_8046899 : Nat := 4983230072969 + 3 ^ 40 * 8046899 * 2
def baseEnd_8046899 : Nat := 4131926965184017204355491

theorem tailTrace_8046899 : CollatzResearch.WordTrace tailWord_8046899 prefixEnd_8046899 4131926965184017204355491 := by
  unfold tailWord_8046899
  simp only [CollatzResearch.WordTrace]
  refine ⟨293494518074466698780623751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195663012049644465853749167 293494518074466698780623751)
  ·
    refine ⟨440241777111700048170935627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293494518074466698780623751 440241777111700048170935627)
    ·
      refine ⟨660362665667550072256403441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440241777111700048170935627 660362665667550072256403441)
      ·
        refine ⟨495271999250662554192302581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660362665667550072256403441 495271999250662554192302581)
        ·
          refine ⟨46431749929749614455528367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 495271999250662554192302581 46431749929749614455528367)
          ·
            refine ⟨69647624894624421683292551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46431749929749614455528367 69647624894624421683292551)
            ·
              refine ⟨104471437341936632524938827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69647624894624421683292551 104471437341936632524938827)
              ·
                refine ⟨156707156012904948787408241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104471437341936632524938827 156707156012904948787408241)
                ·
                  refine ⟨117530367009678711590556181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 156707156012904948787408241 117530367009678711590556181)
                  ·
                    refine ⟨5509235953578689605807321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 117530367009678711590556181 5509235953578689605807321)
                    ·
                      refine ⟨4131926965184017204355491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5509235953578689605807321 4131926965184017204355491)
                      ·
                        rfl

theorem cell23_8046899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 6, 2].length) (baseStart_8046899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046899 prefixEnd_8046899 := by exact prefixLift 8046899
  have htrace : WordTrace (prefixWord ++ tailWord_8046899) baseStart_8046899 baseEnd_8046899 := by
    simpa [prefixWord, tailWord_8046899, baseEnd_8046899] using wordTrace_append hprefix tailTrace_8046899
  have hstable : (prefixWord ++ tailWord_8046899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046899).length < 2 ^ (prefixWord ++ tailWord_8046899).sum := by decide
  have hdescent : baseEnd_8046899 < baseStart_8046899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046910 : List Nat := [4, 2, 1, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_8046910 : Nat := 118140960795 + 8046910 * 2 ^ 59
def prefixEnd_8046910 : Nat := 4983230072969 + 3 ^ 40 * 8046910 * 2
def baseEnd_8046910 : Nat := 4131932613471216661317941

theorem tailTrace_8046910 : CollatzResearch.WordTrace tailWord_8046910 prefixEnd_8046910 4131932613471216661317941 := by
  unfold tailWord_8046910
  simp only [CollatzResearch.WordTrace]
  refine ⟨36686864909678355957409273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195663279518284565106182789 36686864909678355957409273)
  ·
    refine ⟨27515148682258766968056955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36686864909678355957409273 27515148682258766968056955)
    ·
      refine ⟨41272723023388150452085433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27515148682258766968056955 41272723023388150452085433)
      ·
        refine ⟨30954542267541112839064075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41272723023388150452085433 30954542267541112839064075)
        ·
          refine ⟨46431813401311669258596113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30954542267541112839064075 46431813401311669258596113)
          ·
            refine ⟨34823860050983751943947085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46431813401311669258596113 34823860050983751943947085)
            ·
              refine ⟨13058947519118906978980157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34823860050983751943947085 13058947519118906978980157)
              ·
                refine ⟨4897105319669590117117559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13058947519118906978980157 4897105319669590117117559)
                ·
                  refine ⟨7345657979504385175676339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4897105319669590117117559 7345657979504385175676339)
                  ·
                    refine ⟨11018486969256577763514509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7345657979504385175676339 11018486969256577763514509)
                    ·
                      refine ⟨4131932613471216661317941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11018486969256577763514509 4131932613471216661317941)
                      ·
                        rfl

theorem cell23_8046910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_8046910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046910 prefixEnd_8046910 := by exact prefixLift 8046910
  have htrace : WordTrace (prefixWord ++ tailWord_8046910) baseStart_8046910 baseEnd_8046910 := by
    simpa [prefixWord, tailWord_8046910, baseEnd_8046910] using wordTrace_append hprefix tailTrace_8046910
  have hstable : (prefixWord ++ tailWord_8046910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046910).length < 2 ^ (prefixWord ++ tailWord_8046910).sum := by decide
  have hdescent : baseEnd_8046910 < baseStart_8046910 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046919 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 5]
def baseStart_8046919 : Nat := 118140960795 + 8046919 * 2 ^ 59
def prefixEnd_8046919 : Nat := 4983230072969 + 3 ^ 40 * 8046919 * 2
def baseEnd_8046919 : Nat := 4131937234797107126105399

theorem tailTrace_8046919 : CollatzResearch.WordTrace tailWord_8046919 prefixEnd_8046919 4131937234797107126105399 := by
  unfold tailWord_8046919
  simp only [CollatzResearch.WordTrace]
  refine ⟨293495247534394242196351811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195663498356262828130901207 293495247534394242196351811)
  ·
    refine ⟨440242871301591363294527717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293495247534394242196351811 440242871301591363294527717)
    ·
      refine ⟨82545538369048380617723947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440242871301591363294527717 82545538369048380617723947)
      ·
        refine ⟨123818307553572570926585921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82545538369048380617723947 123818307553572570926585921)
        ·
          refine ⟨92863730665179428194939441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123818307553572570926585921 92863730665179428194939441)
          ·
            refine ⟨69647797998884571146204581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92863730665179428194939441 69647797998884571146204581)
            ·
              refine ⟨13058962124790857089913359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69647797998884571146204581 13058962124790857089913359)
              ·
                refine ⟨19588443187186285634870039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13058962124790857089913359 19588443187186285634870039)
                ·
                  refine ⟨29382664780779428452305059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19588443187186285634870039 29382664780779428452305059)
                  ·
                    refine ⟨44073997171169142678457589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29382664780779428452305059 44073997171169142678457589)
                    ·
                      refine ⟨4131937234797107126105399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44073997171169142678457589 4131937234797107126105399)
                      ·
                        rfl

theorem cell23_8046919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_8046919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046919 prefixEnd_8046919 := by exact prefixLift 8046919
  have htrace : WordTrace (prefixWord ++ tailWord_8046919) baseStart_8046919 baseEnd_8046919 := by
    simpa [prefixWord, tailWord_8046919, baseEnd_8046919] using wordTrace_append hprefix tailTrace_8046919
  have hstable : (prefixWord ++ tailWord_8046919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046919).length < 2 ^ (prefixWord ++ tailWord_8046919).sum := by decide
  have hdescent : baseEnd_8046919 < baseStart_8046919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8046983 : List Nat := [1, 1, 4, 2, 2, 1, 4, 2, 2, 1, 3]
def baseStart_8046983 : Nat := 118140960795 + 8046983 * 2 ^ 59
def prefixEnd_8046983 : Nat := 4983230072969 + 3 ^ 40 * 8046983 * 2
def baseEnd_8046983 : Nat := 4131970097558994875705105

theorem tailTrace_8046983 : CollatzResearch.WordTrace tailWord_8046983 prefixEnd_8046983 4131970097558994875705105 := by
  unfold tailWord_8046983
  simp only [CollatzResearch.WordTrace]
  refine ⟨293497581806162381126681603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195665054537441587417787735 293497581806162381126681603)
  ·
    refine ⟨440246372709243571690022405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293497581806162381126681603 440246372709243571690022405)
    ·
      refine ⟨82546194882983169691879201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440246372709243571690022405 82546194882983169691879201)
      ·
        refine ⟨61909646162237377268909401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82546194882983169691879201 61909646162237377268909401)
        ·
          refine ⟨46432234621678032951682051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61909646162237377268909401 46432234621678032951682051)
          ·
            refine ⟨69648351932517049427523077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46432234621678032951682051 69648351932517049427523077)
            ·
              refine ⟨13059065987346946767660577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 69648351932517049427523077 13059065987346946767660577)
              ·
                refine ⟨9794299490510210075745433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13059065987346946767660577 9794299490510210075745433)
                ·
                  refine ⟨7345724617882657556809075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9794299490510210075745433 7345724617882657556809075)
                  ·
                    refine ⟨11018586926823986335213613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7345724617882657556809075 11018586926823986335213613)
                    ·
                      refine ⟨4131970097558994875705105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11018586926823986335213613 4131970097558994875705105)
                      ·
                        rfl

theorem cell23_8046983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_8046983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8046983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8046983 prefixEnd_8046983 := by exact prefixLift 8046983
  have htrace : WordTrace (prefixWord ++ tailWord_8046983) baseStart_8046983 baseEnd_8046983 := by
    simpa [prefixWord, tailWord_8046983, baseEnd_8046983] using wordTrace_append hprefix tailTrace_8046983
  have hstable : (prefixWord ++ tailWord_8046983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8046983).length < 2 ^ (prefixWord ++ tailWord_8046983).sum := by decide
  have hdescent : baseEnd_8046983 < baseStart_8046983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8046983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047036 : List Nat := [2, 2, 2, 4, 1, 1, 1, 2, 2, 2, 4]
def baseStart_8047036 : Nat := 118140960795 + 8047036 * 2 ^ 59
def prefixEnd_8047036 : Nat := 4983230072969 + 3 ^ 40 * 8047036 * 2
def baseEnd_8047036 : Nat := 4131997312033683168342361

theorem tailTrace_8047036 : CollatzResearch.WordTrace tailWord_8047036 prefixEnd_8047036 4131997312033683168342361 := by
  unfold tailWord_8047036
  simp only [CollatzResearch.WordTrace]
  refine ⟨146749757437485185589180481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195666343249980247452240641 146749757437485185589180481)
  ·
    refine ⟨110062318078113889191885361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146749757437485185589180481 110062318078113889191885361)
    ·
      refine ⟨82546738558585416893914021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110062318078113889191885361 82546738558585416893914021)
      ·
        refine ⟨15477513479734765667608879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82546738558585416893914021 15477513479734765667608879)
        ·
          refine ⟨23216270219602148501413319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15477513479734765667608879 23216270219602148501413319)
          ·
            refine ⟨34824405329403222752119979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23216270219602148501413319 34824405329403222752119979)
            ·
              refine ⟨52236607994104834128179969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34824405329403222752119979 52236607994104834128179969)
              ·
                refine ⟨39177455995578625596134977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52236607994104834128179969 39177455995578625596134977)
                ·
                  refine ⟨29383091996683969197101233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 39177455995578625596134977 29383091996683969197101233)
                  ·
                    refine ⟨22037318997512976897825925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29383091996683969197101233 22037318997512976897825925)
                    ·
                      refine ⟨4131997312033683168342361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22037318997512976897825925 4131997312033683168342361)
                      ·
                        rfl

theorem cell23_8047036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_8047036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047036 prefixEnd_8047036 := by exact prefixLift 8047036
  have htrace : WordTrace (prefixWord ++ tailWord_8047036) baseStart_8047036 baseEnd_8047036 := by
    simpa [prefixWord, tailWord_8047036, baseEnd_8047036] using wordTrace_append hprefix tailTrace_8047036
  have hstable : (prefixWord ++ tailWord_8047036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047036).length < 2 ^ (prefixWord ++ tailWord_8047036).sum := by decide
  have hdescent : baseEnd_8047036 < baseStart_8047036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047096 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 2, 1, 4]
def baseStart_8047096 : Nat := 118140960795 + 8047096 * 2 ^ 59
def prefixEnd_8047096 : Nat := 4983230072969 + 3 ^ 40 * 8047096 * 2
def baseEnd_8047096 : Nat := 4132028120872952933592085

theorem tailTrace_8047096 : CollatzResearch.WordTrace tailWord_8047096 prefixEnd_8047096 4132028120872952933592085 := by
  unfold tailWord_8047096
  simp only [CollatzResearch.WordTrace]
  refine ⟨146750851627376500712772571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195667802169835334283696761 146750851627376500712772571)
  ·
    refine ⟨220126277441064751069158857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146750851627376500712772571 220126277441064751069158857)
    ·
      refine ⟨165094708080798563301869143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220126277441064751069158857 165094708080798563301869143)
      ·
        refine ⟨247642062121197844952803715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165094708080798563301869143 247642062121197844952803715)
        ·
          refine ⟨371463093181796767429205573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247642062121197844952803715 371463093181796767429205573)
          ·
            refine ⟨69649329971586893892976045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 371463093181796767429205573 69649329971586893892976045)
            ·
              refine ⟨26118498739345085209866017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69649329971586893892976045 26118498739345085209866017)
              ·
                refine ⟨19588874054508813907399513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26118498739345085209866017 19588874054508813907399513)
                ·
                  refine ⟨14691655540881610430549635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19588874054508813907399513 14691655540881610430549635)
                  ·
                    refine ⟨22037483311322415645824453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14691655540881610430549635 22037483311322415645824453)
                    ·
                      refine ⟨4132028120872952933592085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22037483311322415645824453 4132028120872952933592085)
                      ·
                        rfl

theorem cell23_8047096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 2, 1, 4].length) (baseStart_8047096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047096 prefixEnd_8047096 := by exact prefixLift 8047096
  have htrace : WordTrace (prefixWord ++ tailWord_8047096) baseStart_8047096 baseEnd_8047096 := by
    simpa [prefixWord, tailWord_8047096, baseEnd_8047096] using wordTrace_append hprefix tailTrace_8047096
  have hstable : (prefixWord ++ tailWord_8047096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047096).length < 2 ^ (prefixWord ++ tailWord_8047096).sum := by decide
  have hdescent : baseEnd_8047096 < baseStart_8047096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047109 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 6]
def baseStart_8047109 : Nat := 118140960795 + 8047109 * 2 ^ 59
def prefixEnd_8047109 : Nat := 4983230072969 + 3 ^ 40 * 8047109 * 2
def baseEnd_8047109 : Nat := 4132034796121461382729525

theorem tailTrace_8047109 : CollatzResearch.WordTrace tailWord_8047109 prefixEnd_8047109 4132034796121461382729525 := by
  unfold tailWord_8047109
  simp only [CollatzResearch.WordTrace]
  refine ⟨293502177403705904645768381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195668118269137269763845587 293502177403705904645768381)
  ·
    refine ⟨110063316526389714242163143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293502177403705904645768381 110063316526389714242163143)
    ·
      refine ⟨165094974789584571363244715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110063316526389714242163143 165094974789584571363244715)
      ·
        refine ⟨247642462184376857044867073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165094974789584571363244715 247642462184376857044867073)
        ·
          refine ⟨185731846638282642783650305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247642462184376857044867073 185731846638282642783650305)
          ·
            refine ⟨139298884978711982087737729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185731846638282642783650305 139298884978711982087737729)
            ·
              refine ⟨104474163734033986565803297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139298884978711982087737729 104474163734033986565803297)
              ·
                refine ⟨78355622800525489924352473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104474163734033986565803297 78355622800525489924352473)
                ·
                  refine ⟨58766717100394117443264355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 78355622800525489924352473 58766717100394117443264355)
                  ·
                    refine ⟨88150075650591176164896533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58766717100394117443264355 88150075650591176164896533)
                    ·
                      refine ⟨4132034796121461382729525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88150075650591176164896533 4132034796121461382729525)
                      ·
                        rfl

theorem cell23_8047109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_8047109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047109 prefixEnd_8047109 := by exact prefixLift 8047109
  have htrace : WordTrace (prefixWord ++ tailWord_8047109) baseStart_8047109 baseEnd_8047109 := by
    simpa [prefixWord, tailWord_8047109, baseEnd_8047109] using wordTrace_append hprefix tailTrace_8047109
  have hstable : (prefixWord ++ tailWord_8047109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047109).length < 2 ^ (prefixWord ++ tailWord_8047109).sum := by decide
  have hdescent : baseEnd_8047109 < baseStart_8047109 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047133 : List Nat := [1, 4, 2, 2, 1, 2, 1, 3, 2, 2, 3]
def baseStart_8047133 : Nat := 118140960795 + 8047133 * 2 ^ 59
def prefixEnd_8047133 : Nat := 4983230072969 + 3 ^ 40 * 8047133 * 2
def baseEnd_8047133 : Nat := 4132047119657169288829415

theorem tailTrace_8047133 : CollatzResearch.WordTrace tailWord_8047133 prefixEnd_8047133 4132047119657169288829415 := by
  unfold tailWord_8047133
  simp only [CollatzResearch.WordTrace]
  refine ⟨293503052755618956744642053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195668701837079304496428035 293503052755618956744642053)
  ·
    refine ⟨55031822391678554389620385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293503052755618956744642053 55031822391678554389620385)
    ·
      refine ⟨41273866793758915792215289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55031822391678554389620385 41273866793758915792215289)
      ·
        refine ⟨30955400095319186844161467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41273866793758915792215289 30955400095319186844161467)
        ·
          refine ⟨46433100142978780266242201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30955400095319186844161467 46433100142978780266242201)
          ·
            refine ⟨34824825107234085199681651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46433100142978780266242201 34824825107234085199681651)
            ·
              refine ⟨52237237660851127799522477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34824825107234085199681651 52237237660851127799522477)
              ·
                refine ⟨19588964122819172924820929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52237237660851127799522477 19588964122819172924820929)
                ·
                  refine ⟨14691723092114379693615697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19588964122819172924820929 14691723092114379693615697)
                  ·
                    refine ⟨11018792319085784770211773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14691723092114379693615697 11018792319085784770211773)
                    ·
                      refine ⟨4132047119657169288829415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11018792319085784770211773 4132047119657169288829415)
                      ·
                        rfl

theorem cell23_8047133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 2, 3].length) (baseStart_8047133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047133 prefixEnd_8047133 := by exact prefixLift 8047133
  have htrace : WordTrace (prefixWord ++ tailWord_8047133) baseStart_8047133 baseEnd_8047133 := by
    simpa [prefixWord, tailWord_8047133, baseEnd_8047133] using wordTrace_append hprefix tailTrace_8047133
  have hstable : (prefixWord ++ tailWord_8047133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047133).length < 2 ^ (prefixWord ++ tailWord_8047133).sum := by decide
  have hdescent : baseEnd_8047133 < baseStart_8047133 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047203 : List Nat := [1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 4]
def baseStart_8047203 : Nat := 118140960795 + 8047203 * 2 ^ 59
def prefixEnd_8047203 : Nat := 4983230072969 + 3 ^ 40 * 8047203 * 2
def baseEnd_8047203 : Nat := 4132083063302984014954093

theorem tailTrace_8047203 : CollatzResearch.WordTrace tailWord_8047203 prefixEnd_8047203 4132083063302984014954093 := by
  unfold tailWord_8047203
  simp only [CollatzResearch.WordTrace]
  refine ⟨293505605865365358699690263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195670403910243572466460175 293505605865365358699690263)
  ·
    refine ⟨440258408798048038049535395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293505605865365358699690263 440258408798048038049535395)
    ·
      refine ⟨660387613197072057074303093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440258408798048038049535395 660387613197072057074303093)
      ·
        refine ⟨61911338737225505350715915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 660387613197072057074303093 61911338737225505350715915)
        ·
          refine ⟨92867008105838258026073873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61911338737225505350715915 92867008105838258026073873)
          ·
            refine ⟨69650256079378693519555405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92867008105838258026073873 69650256079378693519555405)
            ·
              refine ⟨26118846029767010069833277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69650256079378693519555405 26118846029767010069833277)
              ·
                refine ⟨9794567261162628776187479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26118846029767010069833277 9794567261162628776187479)
                ·
                  refine ⟨14691850891743943164281219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9794567261162628776187479 14691850891743943164281219)
                  ·
                    refine ⟨22037776337615914746421829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14691850891743943164281219 22037776337615914746421829)
                    ·
                      refine ⟨4132083063302984014954093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22037776337615914746421829 4132083063302984014954093)
                      ·
                        rfl

theorem cell23_8047203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_8047203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047203 prefixEnd_8047203 := by exact prefixLift 8047203
  have htrace : WordTrace (prefixWord ++ tailWord_8047203) baseStart_8047203 baseEnd_8047203 := by
    simpa [prefixWord, tailWord_8047203, baseEnd_8047203] using wordTrace_append hprefix tailTrace_8047203
  have hstable : (prefixWord ++ tailWord_8047203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047203).length < 2 ^ (prefixWord ++ tailWord_8047203).sum := by decide
  have hdescent : baseEnd_8047203 < baseStart_8047203 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047271 : List Nat := [1, 1, 6, 3, 1, 2, 1, 1, 3, 2, 2]
def baseStart_8047271 : Nat := 118140960795 + 8047271 * 2 ^ 59
def prefixEnd_8047271 : Nat := 4983230072969 + 3 ^ 40 * 8047271 * 2
def baseEnd_8047271 : Nat := 4132117979987489748903781

theorem tailTrace_8047271 : CollatzResearch.WordTrace tailWord_8047271 prefixEnd_8047271 4132117979987489748903781 := by
  unfold tailWord_8047271
  simp only [CollatzResearch.WordTrace]
  refine ⟨293508086029119006313165667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195672057352746004208777111 293508086029119006313165667)
  ·
    refine ⟨440262129043678509469748501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293508086029119006313165667 440262129043678509469748501)
    ·
      refine ⟨20637287298922430131394461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 440262129043678509469748501 20637287298922430131394461)
      ·
        refine ⟨7738982737095911299272923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20637287298922430131394461 7738982737095911299272923)
        ·
          refine ⟨11608474105643866948909385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7738982737095911299272923 11608474105643866948909385)
          ·
            refine ⟨8706355579232900211682039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11608474105643866948909385 8706355579232900211682039)
            ·
              refine ⟨13059533368849350317523059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8706355579232900211682039 13059533368849350317523059)
              ·
                refine ⟨19589300053274025476284589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13059533368849350317523059 19589300053274025476284589)
                ·
                  refine ⟨7345987519977759553606721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19589300053274025476284589 7345987519977759553606721)
                  ·
                    refine ⟨5509490639983319665205041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7345987519977759553606721 5509490639983319665205041)
                    ·
                      refine ⟨4132117979987489748903781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5509490639983319665205041 4132117979987489748903781)
                      ·
                        rfl

theorem cell23_8047271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_8047271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047271 prefixEnd_8047271 := by exact prefixLift 8047271
  have htrace : WordTrace (prefixWord ++ tailWord_8047271) baseStart_8047271 baseEnd_8047271 := by
    simpa [prefixWord, tailWord_8047271, baseEnd_8047271] using wordTrace_append hprefix tailTrace_8047271
  have hstable : (prefixWord ++ tailWord_8047271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047271).length < 2 ^ (prefixWord ++ tailWord_8047271).sum := by decide
  have hdescent : baseEnd_8047271 < baseStart_8047271 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047281 : List Nat := [1, 2, 2, 6, 2, 1, 2, 1, 2, 4]
def baseStart_8047281 : Nat := 118140960795 + 8047281 * 2 ^ 59
def prefixEnd_8047281 : Nat := 4983230072969 + 3 ^ 40 * 8047281 * 2
def baseEnd_8047281 : Nat := 1377374371598011569926245

theorem tailTrace_8047281 : CollatzResearch.WordTrace tailWord_8047281 prefixEnd_8047281 1377374371598011569926245 := by
  unfold tailWord_8047281
  simp only [CollatzResearch.WordTrace]
  refine ⟨293508450759082778021029697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195672300506055185347353131 293508450759082778021029697)
  ·
    refine ⟨220131338069312083515772273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293508450759082778021029697 220131338069312083515772273)
    ·
      refine ⟨165098503551984062636829205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220131338069312083515772273 165098503551984062636829205)
      ·
        refine ⟨7738992353999252936101369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 165098503551984062636829205 7738992353999252936101369)
        ·
          refine ⟨5804244265499439702076027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7738992353999252936101369 5804244265499439702076027)
          ·
            refine ⟨8706366398249159553114041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804244265499439702076027 8706366398249159553114041)
            ·
              refine ⟨6529774798686869664835531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8706366398249159553114041 6529774798686869664835531)
              ·
                refine ⟨9794662198030304497253297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6529774798686869664835531 9794662198030304497253297)
                ·
                  refine ⟨7345996648522728372939973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9794662198030304497253297 7345996648522728372939973)
                  ·
                    refine ⟨1377374371598011569926245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7345996648522728372939973 1377374371598011569926245)
                    ·
                      rfl

theorem cell23_8047281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_8047281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047281 prefixEnd_8047281 := by exact prefixLift 8047281
  have htrace : WordTrace (prefixWord ++ tailWord_8047281) baseStart_8047281 baseEnd_8047281 := by
    simpa [prefixWord, tailWord_8047281, baseEnd_8047281] using wordTrace_append hprefix tailTrace_8047281
  have hstable : (prefixWord ++ tailWord_8047281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047281).length < 2 ^ (prefixWord ++ tailWord_8047281).sum := by decide
  have hdescent : baseEnd_8047281 < baseStart_8047281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047287 : List Nat := [1, 1, 3, 1, 6, 1, 1, 3, 2, 1, 3]
def baseStart_8047287 : Nat := 118140960795 + 8047287 * 2 ^ 59
def prefixEnd_8047287 : Nat := 4983230072969 + 3 ^ 40 * 8047287 * 2
def baseEnd_8047287 : Nat := 4132126195677961686303707

theorem tailTrace_8047287 : CollatzResearch.WordTrace tailWord_8047287 prefixEnd_8047287 4132126195677961686303707 := by
  unfold tailWord_8047287
  simp only [CollatzResearch.WordTrace]
  refine ⟨293508669597061041045748115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195672446398040694030498743 293508669597061041045748115)
  ·
    refine ⟨440263004395591561568622173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293508669597061041045748115 440263004395591561568622173)
    ·
      refine ⟨165098626648346835588233315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440263004395591561568622173 165098626648346835588233315)
      ·
        refine ⟨247647939972520253382349973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165098626648346835588233315 247647939972520253382349973)
        ·
          refine ⟨11608497186211886877297655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 247647939972520253382349973 11608497186211886877297655)
          ·
            refine ⟨17412745779317830315946483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11608497186211886877297655 17412745779317830315946483)
            ·
              refine ⟨26119118668976745473919725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17412745779317830315946483 26119118668976745473919725)
              ·
                refine ⟨9794669500866279552719897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26119118668976745473919725 9794669500866279552719897)
                ·
                  refine ⟨7346002125649709664539923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9794669500866279552719897 7346002125649709664539923)
                  ·
                    refine ⟨11019003188474564496809885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7346002125649709664539923 11019003188474564496809885)
                    ·
                      refine ⟨4132126195677961686303707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11019003188474564496809885 4132126195677961686303707)
                      ·
                        rfl

theorem cell23_8047287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 3, 2, 1, 3].length) (baseStart_8047287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047287 prefixEnd_8047287 := by exact prefixLift 8047287
  have htrace : WordTrace (prefixWord ++ tailWord_8047287) baseStart_8047287 baseEnd_8047287 := by
    simpa [prefixWord, tailWord_8047287, baseEnd_8047287] using wordTrace_append hprefix tailTrace_8047287
  have hstable : (prefixWord ++ tailWord_8047287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047287).length < 2 ^ (prefixWord ++ tailWord_8047287).sum := by decide
  have hdescent : baseEnd_8047287 < baseStart_8047287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047310 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2]
def baseStart_8047310 : Nat := 118140960795 + 8047310 * 2 ^ 59
def prefixEnd_8047310 : Nat := 4983230072969 + 3 ^ 40 * 8047310 * 2
def baseEnd_8047310 : Nat := 4132138005733015096316101

theorem tailTrace_8047310 : CollatzResearch.WordTrace tailWord_8047310 prefixEnd_8047310 4132138005733015096316101 := by
  unfold tailWord_8047310
  simp only [CollatzResearch.WordTrace]
  refine ⟨36688688559497214496729423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195673005650651810649223589 36688688559497214496729423)
  ·
    refine ⟨55033032839245821745094135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36688688559497214496729423 55033032839245821745094135)
    ·
      refine ⟨82549549258868732617641203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55033032839245821745094135 82549549258868732617641203)
      ·
        refine ⟨123824323888303098926461805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82549549258868732617641203 123824323888303098926461805)
        ·
          refine ⟨46434121458113662097423177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123824323888303098926461805 46434121458113662097423177)
          ·
            refine ⟨34825591093585246573067383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46434121458113662097423177 34825591093585246573067383)
            ·
              refine ⟨52238386640377869859601075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34825591093585246573067383 52238386640377869859601075)
              ·
                refine ⟨78357579960566804789401613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52238386640377869859601075 78357579960566804789401613)
                ·
                  refine ⟨29384092485212551796025605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78357579960566804789401613 29384092485212551796025605)
                  ·
                    refine ⟨5509517340977353461754801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29384092485212551796025605 5509517340977353461754801)
                    ·
                      refine ⟨4132138005733015096316101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5509517340977353461754801 4132138005733015096316101)
                      ·
                        rfl

theorem cell23_8047310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 3, 4, 2].length) (baseStart_8047310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047310 prefixEnd_8047310 := by exact prefixLift 8047310
  have htrace : WordTrace (prefixWord ++ tailWord_8047310) baseStart_8047310 baseEnd_8047310 := by
    simpa [prefixWord, tailWord_8047310, baseEnd_8047310] using wordTrace_append hprefix tailTrace_8047310
  have hstable : (prefixWord ++ tailWord_8047310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047310).length < 2 ^ (prefixWord ++ tailWord_8047310).sum := by decide
  have hdescent : baseEnd_8047310 < baseStart_8047310 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047327 : List Nat := [1, 1, 2, 3, 2, 3, 1, 4, 2, 2, 2]
def baseStart_8047327 : Nat := 118140960795 + 8047327 * 2 ^ 59
def prefixEnd_8047327 : Nat := 4983230072969 + 3 ^ 40 * 8047327 * 2
def baseEnd_8047327 : Nat := 4132146734904141529803523

theorem tailTrace_8047327 : CollatzResearch.WordTrace tailWord_8047327 prefixEnd_8047327 4132146734904141529803523 := by
  unfold tailWord_8047327
  simp only [CollatzResearch.WordTrace]
  refine ⟨293510128516916127877204235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195673419011277418584802823 293510128516916127877204235)
  ·
    refine ⟨440265192775374191815806353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293510128516916127877204235 440265192775374191815806353)
    ·
      refine ⟨330198894581530643861854765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440265192775374191815806353 330198894581530643861854765)
      ·
        refine ⟨123824585468073991448195537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 330198894581530643861854765 123824585468073991448195537)
        ·
          refine ⟨92868439101055493586146653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123824585468073991448195537 92868439101055493586146653)
          ·
            refine ⟨34825664662895810094804995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 92868439101055493586146653 34825664662895810094804995)
            ·
              refine ⟨52238496994343715142207493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34825664662895810094804995 52238496994343715142207493)
              ·
                refine ⟨9794718186439446589163905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 52238496994343715142207493 9794718186439446589163905)
                ·
                  refine ⟨7346038639829584941872929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9794718186439446589163905 7346038639829584941872929)
                  ·
                    refine ⟨5509528979872188706404697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7346038639829584941872929 5509528979872188706404697)
                    ·
                      refine ⟨4132146734904141529803523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5509528979872188706404697 4132146734904141529803523)
                      ·
                        rfl

theorem cell23_8047327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 2, 2].length) (baseStart_8047327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047327 prefixEnd_8047327 := by exact prefixLift 8047327
  have htrace : WordTrace (prefixWord ++ tailWord_8047327) baseStart_8047327 baseEnd_8047327 := by
    simpa [prefixWord, tailWord_8047327, baseEnd_8047327] using wordTrace_append hprefix tailTrace_8047327
  have hstable : (prefixWord ++ tailWord_8047327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047327).length < 2 ^ (prefixWord ++ tailWord_8047327).sum := by decide
  have hdescent : baseEnd_8047327 < baseStart_8047327 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047343 : List Nat := [1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 3]
def baseStart_8047343 : Nat := 118140960795 + 8047343 * 2 ^ 59
def prefixEnd_8047343 : Nat := 4983230072969 + 3 ^ 40 * 8047343 * 2
def baseEnd_8047343 : Nat := 4132154950594613467203449

theorem tailTrace_8047343 : CollatzResearch.WordTrace tailWord_8047343 prefixEnd_8047343 4132154950594613467203449 := by
  unfold tailWord_8047343
  simp only [CollatzResearch.WordTrace]
  refine ⟨293510712084858162609786683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195673808056572108406524455 293510712084858162609786683)
  ·
    refine ⟨440266068127287243914680025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293510712084858162609786683 440266068127287243914680025)
    ·
      refine ⟨330199551095465432936010019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440266068127287243914680025 330199551095465432936010019)
      ·
        refine ⟨495299326643198149404015029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330199551095465432936010019 495299326643198149404015029)
        ·
          refine ⟨46434311872799826506626409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 495299326643198149404015029 46434311872799826506626409)
          ·
            refine ⟨34825733904599869879969807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46434311872799826506626409 34825733904599869879969807)
            ·
              refine ⟨52238600856899804819954711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34825733904599869879969807 52238600856899804819954711)
              ·
                refine ⟨78357901285349707229932067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52238600856899804819954711 78357901285349707229932067)
                ·
                  refine ⟨117536851928024560844898101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78357901285349707229932067 117536851928024560844898101)
                  ·
                    refine ⟨11019079868252302579209197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117536851928024560844898101 11019079868252302579209197)
                    ·
                      refine ⟨4132154950594613467203449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11019079868252302579209197 4132154950594613467203449)
                      ·
                        rfl

theorem cell23_8047343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 1, 1, 1, 5, 3].length) (baseStart_8047343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047343 prefixEnd_8047343 := by exact prefixLift 8047343
  have htrace : WordTrace (prefixWord ++ tailWord_8047343) baseStart_8047343 baseEnd_8047343 := by
    simpa [prefixWord, tailWord_8047343, baseEnd_8047343] using wordTrace_append hprefix tailTrace_8047343
  have hstable : (prefixWord ++ tailWord_8047343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047343).length < 2 ^ (prefixWord ++ tailWord_8047343).sum := by decide
  have hdescent : baseEnd_8047343 < baseStart_8047343 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047367 : List Nat := [1, 1, 4, 4, 1, 2, 2, 3, 5]
def baseStart_8047367 : Nat := 118140960795 + 8047367 * 2 ^ 59
def prefixEnd_8047367 : Nat := 4983230072969 + 3 ^ 40 * 8047367 * 2
def baseEnd_8047367 : Nat := 459129697125591263700371

theorem tailTrace_8047367 : CollatzResearch.WordTrace tailWord_8047367 prefixEnd_8047367 459129697125591263700371 := by
  unfold tailWord_8047367
  simp only [CollatzResearch.WordTrace]
  refine ⟨293511587436771214708660355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195674391624514143139106903 293511587436771214708660355)
  ·
    refine ⟨440267381155156822062990533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293511587436771214708660355 440267381155156822062990533)
    ·
      refine ⟨82550133966591904136810725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 440267381155156822062990533 82550133966591904136810725)
      ·
        refine ⟨15478150118735982025652011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 82550133966591904136810725 15478150118735982025652011)
        ·
          refine ⟨23217225178103973038478017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15478150118735982025652011 23217225178103973038478017)
          ·
            refine ⟨17412918883577979778858513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23217225178103973038478017 17412918883577979778858513)
            ·
              refine ⟨13059689162683484834143885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17412918883577979778858513 13059689162683484834143885)
              ·
                refine ⟨4897383436006306812803957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13059689162683484834143885 4897383436006306812803957)
                ·
                  refine ⟨459129697125591263700371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4897383436006306812803957 459129697125591263700371)
                  ·
                    rfl

theorem cell23_8047367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 2, 3, 5].length) (baseStart_8047367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047367 prefixEnd_8047367 := by exact prefixLift 8047367
  have htrace : WordTrace (prefixWord ++ tailWord_8047367) baseStart_8047367 baseEnd_8047367 := by
    simpa [prefixWord, tailWord_8047367, baseEnd_8047367] using wordTrace_append hprefix tailTrace_8047367
  have hstable : (prefixWord ++ tailWord_8047367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047367).length < 2 ^ (prefixWord ++ tailWord_8047367).sum := by decide
  have hdescent : baseEnd_8047367 < baseStart_8047367 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047378 : List Nat := [3, 2, 4, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_8047378 : Nat := 118140960795 + 8047378 * 2 ^ 59
def prefixEnd_8047378 : Nat := 4983230072969 + 3 ^ 40 * 8047378 * 2
def baseEnd_8047378 : Nat := 4132172922417520830265789

theorem tailTrace_8047378 : CollatzResearch.WordTrace tailWord_8047378 prefixEnd_8047378 4132172922417520830265789 := by
  unfold tailWord_8047378
  simp only [CollatzResearch.WordTrace]
  refine ⟨73377997159932840896827697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195674659093154242391540525 73377997159932840896827697)
  ·
    refine ⟨55033497869949630672620773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73377997159932840896827697 55033497869949630672620773)
    ·
      refine ⟨10318780850615555751116395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55033497869949630672620773 10318780850615555751116395)
      ·
        refine ⟨15478171275923333626674593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10318780850615555751116395 15478171275923333626674593)
        ·
          refine ⟨11608628456942500220005945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15478171275923333626674593 11608628456942500220005945)
          ·
            refine ⟨8706471342706875165004459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11608628456942500220005945 8706471342706875165004459)
            ·
              refine ⟨13059707014060312747506689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8706471342706875165004459 13059707014060312747506689)
              ·
                refine ⟨9794780260545234560630017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13059707014060312747506689 9794780260545234560630017)
                ·
                  refine ⟨7346085195408925920472513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9794780260545234560630017 7346085195408925920472513)
                  ·
                    refine ⟨5509563896556694440354385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7346085195408925920472513 5509563896556694440354385)
                    ·
                      refine ⟨4132172922417520830265789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5509563896556694440354385 4132172922417520830265789)
                      ·
                        rfl

theorem cell23_8047378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_8047378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047378 prefixEnd_8047378 := by exact prefixLift 8047378
  have htrace : WordTrace (prefixWord ++ tailWord_8047378) baseStart_8047378 baseEnd_8047378 := by
    simpa [prefixWord, tailWord_8047378, baseEnd_8047378] using wordTrace_append hprefix tailTrace_8047378
  have hstable : (prefixWord ++ tailWord_8047378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047378).length < 2 ^ (prefixWord ++ tailWord_8047378).sum := by decide
  have hdescent : baseEnd_8047378 < baseStart_8047378 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047403 : List Nat := [1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 3]
def baseStart_8047403 : Nat := 118140960795 + 8047403 * 2 ^ 59
def prefixEnd_8047403 : Nat := 4983230072969 + 3 ^ 40 * 8047403 * 2
def baseEnd_8047403 : Nat := 4132185759433883232453173

theorem tailTrace_8047403 : CollatzResearch.WordTrace tailWord_8047403 prefixEnd_8047403 4132185759433883232453173 := by
  unfold tailWord_8047403
  simp only [CollatzResearch.WordTrace]
  refine ⟨293512900464640792856970863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195675266976427195237980575 293512900464640792856970863)
  ·
    refine ⟨440269350696961189285456295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293512900464640792856970863 440269350696961189285456295)
    ·
      refine ⟨660404026045441783928184443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440269350696961189285456295 660404026045441783928184443)
      ·
        refine ⟨990606039068162675892276665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660404026045441783928184443 990606039068162675892276665)
        ·
          refine ⟨742954529301122006919207499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990606039068162675892276665 742954529301122006919207499)
          ·
            refine ⟨1114431793951683010378811249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742954529301122006919207499 1114431793951683010378811249)
            ·
              refine ⟨835823845463762257784108437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1114431793951683010378811249 835823845463762257784108437)
              ·
                refine ⟨39179242756113855833630083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 835823845463762257784108437 39179242756113855833630083)
                ·
                  refine ⟨58768864134170783750445125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39179242756113855833630083 58768864134170783750445125)
                  ·
                    refine ⟨11019162025157021953208461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 58768864134170783750445125 11019162025157021953208461)
                    ·
                      refine ⟨4132185759433883232453173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11019162025157021953208461 4132185759433883232453173)
                      ·
                        rfl

theorem cell23_8047403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 1, 4, 3].length) (baseStart_8047403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047403 prefixEnd_8047403 := by exact prefixLift 8047403
  have htrace : WordTrace (prefixWord ++ tailWord_8047403) baseStart_8047403 baseEnd_8047403 := by
    simpa [prefixWord, tailWord_8047403, baseEnd_8047403] using wordTrace_append hprefix tailTrace_8047403
  have hstable : (prefixWord ++ tailWord_8047403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047403).length < 2 ^ (prefixWord ++ tailWord_8047403).sum := by decide
  have hdescent : baseEnd_8047403 < baseStart_8047403 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047410 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 3, 4]
def baseStart_8047410 : Nat := 118140960795 + 8047410 * 2 ^ 59
def prefixEnd_8047410 : Nat := 4983230072969 + 3 ^ 40 * 8047410 * 2
def baseEnd_8047410 : Nat := 1377396451266154901688547

theorem tailTrace_8047410 : CollatzResearch.WordTrace tailWord_8047410 prefixEnd_8047410 1377396451266154901688547 := by
  unfold tailWord_8047410
  simp only [CollatzResearch.WordTrace]
  refine ⟨73378288943903858263118921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195675437183743622034983789 73378288943903858263118921)
  ·
    refine ⟨55033716707927893697339191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 73378288943903858263118921 55033716707927893697339191)
    ·
      refine ⟨82550575061891840546008787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55033716707927893697339191 82550575061891840546008787)
      ·
        refine ⟨123825862592837760819013181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82550575061891840546008787 123825862592837760819013181)
        ·
          refine ⟨46434698472314160307129943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123825862592837760819013181 46434698472314160307129943)
          ·
            refine ⟨69652047708471240460694915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46434698472314160307129943 69652047708471240460694915)
            ·
              refine ⟨104478071562706860691042373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69652047708471240460694915 104478071562706860691042373)
              ·
                refine ⟨19589638418007536379570445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104478071562706860691042373 19589638418007536379570445)
                ·
                  refine ⟨7346114406752826142338917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19589638418007536379570445 7346114406752826142338917)
                  ·
                    refine ⟨1377396451266154901688547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7346114406752826142338917 1377396451266154901688547)
                    ·
                      rfl

theorem cell23_8047410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 3, 4].length) (baseStart_8047410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047410 prefixEnd_8047410 := by exact prefixLift 8047410
  have htrace : WordTrace (prefixWord ++ tailWord_8047410) baseStart_8047410 baseEnd_8047410 := by
    simpa [prefixWord, tailWord_8047410, baseEnd_8047410] using wordTrace_append hprefix tailTrace_8047410
  have hstable : (prefixWord ++ tailWord_8047410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047410).length < 2 ^ (prefixWord ++ tailWord_8047410).sum := by decide
  have hdescent : baseEnd_8047410 < baseStart_8047410 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047420 : List Nat := [2, 2, 2, 2, 1, 1, 1, 5, 2, 2, 3]
def baseStart_8047420 : Nat := 118140960795 + 8047420 * 2 ^ 59
def prefixEnd_8047420 : Nat := 4983230072969 + 3 ^ 40 * 8047420 * 2
def baseEnd_8047420 : Nat := 4132194488605009665940595

theorem tailTrace_8047420 : CollatzResearch.WordTrace tailWord_8047420 prefixEnd_8047420 4132194488605009665940595 := by
  unfold tailWord_8047420
  simp only [CollatzResearch.WordTrace]
  refine ⟨146756760252789602380169857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195675680337052803173559809 146756760252789602380169857)
  ·
    refine ⟨110067570189592201785127393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146756760252789602380169857 110067570189592201785127393)
    ·
      refine ⟨82550677642194151338845545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 110067570189592201785127393 82550677642194151338845545)
      ·
        refine ⟨61913008231645613504134159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82550677642194151338845545 61913008231645613504134159)
        ·
          refine ⟨92869512347468420256201239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61913008231645613504134159 92869512347468420256201239)
          ·
            refine ⟨139304268521202630384301859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92869512347468420256201239 139304268521202630384301859)
            ·
              refine ⟨208956402781803945576452789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139304268521202630384301859 208956402781803945576452789)
              ·
                refine ⟨19589662760794119897792449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 208956402781803945576452789 19589662760794119897792449)
                ·
                  refine ⟨14692247070595589923344337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19589662760794119897792449 14692247070595589923344337)
                  ·
                    refine ⟨11019185302946692442508253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14692247070595589923344337 11019185302946692442508253)
                    ·
                      refine ⟨4132194488605009665940595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11019185302946692442508253 4132194488605009665940595)
                      ·
                        rfl

theorem cell23_8047420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 2, 3].length) (baseStart_8047420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047420 prefixEnd_8047420 := by exact prefixLift 8047420
  have htrace : WordTrace (prefixWord ++ tailWord_8047420) baseStart_8047420 baseEnd_8047420 := by
    simpa [prefixWord, tailWord_8047420, baseEnd_8047420] using wordTrace_append hprefix tailTrace_8047420
  have hstable : (prefixWord ++ tailWord_8047420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047420).length < 2 ^ (prefixWord ++ tailWord_8047420).sum := by decide
  have hdescent : baseEnd_8047420 < baseStart_8047420 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047423 : List Nat := [1, 1, 2, 2, 5, 1, 1, 2, 8]
def baseStart_8047423 : Nat := 118140960795 + 8047423 * 2 ^ 59
def prefixEnd_8047423 : Nat := 4983230072969 + 3 ^ 40 * 8047423 * 2
def baseEnd_8047423 : Nat := 459132892116330350467009

theorem tailTrace_8047423 : CollatzResearch.WordTrace tailWord_8047423 prefixEnd_8047423 459132892116330350467009 := by
  unfold tailWord_8047423
  simp only [CollatzResearch.WordTrace]
  refine ⟨293513629924568336272698923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195675753283045557515132615 293513629924568336272698923)
  ·
    refine ⟨440270444886852504409048385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293513629924568336272698923 440270444886852504409048385)
    ·
      refine ⟨330202833665139378306786289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440270444886852504409048385 330202833665139378306786289)
      ·
        refine ⟨247652125248854533730089717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330202833665139378306786289 247652125248854533730089717)
        ·
          refine ⟨23217386742080112537195911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247652125248854533730089717 23217386742080112537195911)
          ·
            refine ⟨34826080113120168805793867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23217386742080112537195911 34826080113120168805793867)
            ·
              refine ⟨52239120169680253208690801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34826080113120168805793867 52239120169680253208690801)
              ·
                refine ⟨39179340127260189906518101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52239120169680253208690801 39179340127260189906518101)
                ·
                  refine ⟨459132892116330350467009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39179340127260189906518101 459132892116330350467009)
                  ·
                    rfl

theorem cell23_8047423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 1, 1, 2, 8].length) (baseStart_8047423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047423 prefixEnd_8047423 := by exact prefixLift 8047423
  have htrace : WordTrace (prefixWord ++ tailWord_8047423) baseStart_8047423 baseEnd_8047423 := by
    simpa [prefixWord, tailWord_8047423, baseEnd_8047423] using wordTrace_append hprefix tailTrace_8047423
  have hstable : (prefixWord ++ tailWord_8047423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047423).length < 2 ^ (prefixWord ++ tailWord_8047423).sum := by decide
  have hdescent : baseEnd_8047423 < baseStart_8047423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047444 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 3, 4]
def baseStart_8047444 : Nat := 118140960795 + 8047444 * 2 ^ 59
def prefixEnd_8047444 : Nat := 4983230072969 + 3 ^ 40 * 8047444 * 2
def baseEnd_8047444 : Nat := 1377402270713572524013495

theorem tailTrace_8047444 : CollatzResearch.WordTrace tailWord_8047444 prefixEnd_8047444 1377402270713572524013495 := by
  unfold tailWord_8047444
  simp only [CollatzResearch.WordTrace]
  refine ⟨146757197928746128429606693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195676263904994837906142257 146757197928746128429606693)
  ·
    refine ⟨27516974611639899080551255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 146757197928746128429606693 27516974611639899080551255)
    ·
      refine ⟨41275461917459848620826883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27516974611639899080551255 41275461917459848620826883)
      ·
        refine ⟨61913192876189772931240325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41275461917459848620826883 61913192876189772931240325)
        ·
          refine ⟨11608723664285582424607561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61913192876189772931240325 11608723664285582424607561)
          ·
            refine ⟨8706542748214186818455671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11608723664285582424607561 8706542748214186818455671)
            ·
              refine ⟨13059814122321280227683507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8706542748214186818455671 13059814122321280227683507)
              ·
                refine ⟨19589721183481920341525261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13059814122321280227683507 19589721183481920341525261)
                ·
                  refine ⟨7346145443805720128071973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19589721183481920341525261 7346145443805720128071973)
                  ·
                    refine ⟨1377402270713572524013495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7346145443805720128071973 1377402270713572524013495)
                    ·
                      rfl

theorem cell23_8047444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_8047444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047444 prefixEnd_8047444 := by exact prefixLift 8047444
  have htrace : WordTrace (prefixWord ++ tailWord_8047444) baseStart_8047444 baseEnd_8047444 := by
    simpa [prefixWord, tailWord_8047444, baseEnd_8047444] using wordTrace_append hprefix tailTrace_8047444
  have hstable : (prefixWord ++ tailWord_8047444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047444).length < 2 ^ (prefixWord ++ tailWord_8047444).sum := by decide
  have hdescent : baseEnd_8047444 < baseStart_8047444 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047483 : List Nat := [1, 1, 1, 1, 1, 5, 3, 1, 3, 6]
def baseStart_8047483 : Nat := 118140960795 + 8047483 * 2 ^ 59
def prefixEnd_8047483 : Nat := 4983230072969 + 3 ^ 40 * 8047483 * 2
def baseEnd_8047483 : Nat := 1377408945962080973150935

theorem tailTrace_8047483 : CollatzResearch.WordTrace tailWord_8047483 prefixEnd_8047483 1377408945962080973150935 := by
  unfold tailWord_8047483
  simp only [CollatzResearch.WordTrace]
  refine ⟨293515818304350966519883103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195677212202900644346588735 293515818304350966519883103)
  ·
    refine ⟨440273727456526449779824655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293515818304350966519883103 440273727456526449779824655)
    ·
      refine ⟨660410591184789674669736983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440273727456526449779824655 660410591184789674669736983)
      ·
        refine ⟨990615886777184512004605475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660410591184789674669736983 990615886777184512004605475)
        ·
          refine ⟨1485923830165776768006908213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990615886777184512004605475 1485923830165776768006908213)
          ·
            refine ⟨139305359078041572000647645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1485923830165776768006908213 139305359078041572000647645)
            ·
              refine ⟨52239509654265589500242867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139305359078041572000647645 52239509654265589500242867)
              ·
                refine ⟨78359264481398384250364301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52239509654265589500242867 78359264481398384250364301)
                ·
                  refine ⟨29384724180524394093886613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78359264481398384250364301 29384724180524394093886613)
                  ·
                    refine ⟨1377408945962080973150935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 29384724180524394093886613 1377408945962080973150935)
                    ·
                      rfl

theorem cell23_8047483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 3, 1, 3, 6].length) (baseStart_8047483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047483 prefixEnd_8047483 := by exact prefixLift 8047483
  have htrace : WordTrace (prefixWord ++ tailWord_8047483) baseStart_8047483 baseEnd_8047483 := by
    simpa [prefixWord, tailWord_8047483, baseEnd_8047483] using wordTrace_append hprefix tailTrace_8047483
  have hstable : (prefixWord ++ tailWord_8047483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047483).length < 2 ^ (prefixWord ++ tailWord_8047483).sum := by decide
  have hdescent : baseEnd_8047483 < baseStart_8047483 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047500 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 4, 4]
def baseStart_8047500 : Nat := 118140960795 + 8047500 * 2 ^ 59
def prefixEnd_8047500 : Nat := 4983230072969 + 3 ^ 40 * 8047500 * 2
def baseEnd_8047500 : Nat := 1377411855685789784313409

theorem tailTrace_8047500 : CollatzResearch.WordTrace tailWord_8047500 prefixEnd_8047500 1377411855685789784313409 := by
  unfold tailWord_8047500
  simp only [CollatzResearch.WordTrace]
  refine ⟨146758219172644689211625977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195677625563526252282167969 146758219172644689211625977)
  ·
    refine ⟨110068664379483516908719483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146758219172644689211625977 110068664379483516908719483)
    ·
      refine ⟨165102996569225275363079225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110068664379483516908719483 165102996569225275363079225)
      ·
        refine ⟨123827247426918956522309419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165102996569225275363079225 123827247426918956522309419)
        ·
          refine ⟨185740871140378434783464129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123827247426918956522309419 185740871140378434783464129)
          ·
            refine ⟨139305653355283826087598097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185740871140378434783464129 139305653355283826087598097)
            ·
              refine ⟨104479240016462869565698573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139305653355283826087598097 104479240016462869565698573)
              ·
                refine ⟨39179715006173576087136965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 104479240016462869565698573 39179715006173576087136965)
                ·
                  refine ⟨7346196563657545516338181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 39179715006173576087136965 7346196563657545516338181)
                  ·
                    refine ⟨1377411855685789784313409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7346196563657545516338181 1377411855685789784313409)
                    ·
                      rfl

theorem cell23_8047500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 4, 4].length) (baseStart_8047500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047500 prefixEnd_8047500 := by exact prefixLift 8047500
  have htrace : WordTrace (prefixWord ++ tailWord_8047500) baseStart_8047500 baseEnd_8047500 := by
    simpa [prefixWord, tailWord_8047500, baseEnd_8047500] using wordTrace_append hprefix tailTrace_8047500
  have hstable : (prefixWord ++ tailWord_8047500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047500).length < 2 ^ (prefixWord ++ tailWord_8047500).sum := by decide
  have hdescent : baseEnd_8047500 < baseStart_8047500 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047517 : List Nat := [1, 4, 2, 1, 2, 1, 1, 5, 2, 4]
def baseStart_8047517 : Nat := 118140960795 + 8047517 * 2 ^ 59
def prefixEnd_8047517 : Nat := 4983230072969 + 3 ^ 40 * 8047517 * 2
def baseEnd_8047517 : Nat := 1377414765409498595475883

theorem tailTrace_8047517 : CollatzResearch.WordTrace tailWord_8047517 prefixEnd_8047517 1377414765409498595475883 := by
  unfold tailWord_8047517
  simp only [CollatzResearch.WordTrace]
  refine ⟨293517058386227790326620805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195678038924151860217747203 293517058386227790326620805)
  ·
    refine ⟨55034448447417710686241401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293517058386227790326620805 55034448447417710686241401)
    ·
      refine ⟨41275836335563283014681051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55034448447417710686241401 41275836335563283014681051)
      ·
        refine ⟨61913754503344924522021577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41275836335563283014681051 61913754503344924522021577)
        ·
          refine ⟨46435315877508693391516183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61913754503344924522021577 46435315877508693391516183)
          ·
            refine ⟨69652973816263040087274275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46435315877508693391516183 69652973816263040087274275)
            ·
              refine ⟨104479460724394560130911413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69652973816263040087274275 104479460724394560130911413)
              ·
                refine ⟨9794949442911990012272945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 104479460724394560130911413 9794949442911990012272945)
                ·
                  refine ⟨7346212082183992509204709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9794949442911990012272945 7346212082183992509204709)
                  ·
                    refine ⟨1377414765409498595475883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7346212082183992509204709 1377414765409498595475883)
                    ·
                      rfl

theorem cell23_8047517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 2, 4].length) (baseStart_8047517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047517 prefixEnd_8047517 := by exact prefixLift 8047517
  have htrace : WordTrace (prefixWord ++ tailWord_8047517) baseStart_8047517 baseEnd_8047517 := by
    simpa [prefixWord, tailWord_8047517, baseEnd_8047517] using wordTrace_append hprefix tailTrace_8047517
  have hstable : (prefixWord ++ tailWord_8047517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047517).length < 2 ^ (prefixWord ++ tailWord_8047517).sum := by decide
  have hdescent : baseEnd_8047517 < baseStart_8047517 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047520 : List Nat := [2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 4]
def baseStart_8047520 : Nat := 118140960795 + 8047520 * 2 ^ 59
def prefixEnd_8047520 : Nat := 4983230072969 + 3 ^ 40 * 8047520 * 2
def baseEnd_8047520 : Nat := 4132245836670459274690135

theorem tailTrace_8047520 : CollatzResearch.WordTrace tailWord_8047520 prefixEnd_8047520 4132245836670459274690135 := by
  unfold tailWord_8047520
  simp only [CollatzResearch.WordTrace]
  refine ⟨146758583902608460919490007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195678111870144614559320009 146758583902608460919490007)
  ·
    refine ⟨220137875853912691379235011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146758583902608460919490007 220137875853912691379235011)
    ·
      refine ⟨330206813780869037068852517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220137875853912691379235011 330206813780869037068852517)
      ·
        refine ⟨61913777583912944450409847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 330206813780869037068852517 61913777583912944450409847)
        ·
          refine ⟨92870666375869416675614771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61913777583912944450409847 92870666375869416675614771)
          ·
            refine ⟨139305999563804125013422157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92870666375869416675614771 139305999563804125013422157)
            ·
              refine ⟨52239749836426546880033309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139305999563804125013422157 52239749836426546880033309)
              ·
                refine ⟨19589906188659955080012491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52239749836426546880033309 19589906188659955080012491)
                ·
                  refine ⟨29384859282989932620018737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19589906188659955080012491 29384859282989932620018737)
                  ·
                    refine ⟨22038644462242449465014053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29384859282989932620018737 22038644462242449465014053)
                    ·
                      refine ⟨4132245836670459274690135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22038644462242449465014053 4132245836670459274690135)
                      ·
                        rfl

theorem cell23_8047520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 1, 2, 4].length) (baseStart_8047520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047520 prefixEnd_8047520 := by exact prefixLift 8047520
  have htrace : WordTrace (prefixWord ++ tailWord_8047520) baseStart_8047520 baseEnd_8047520 := by
    simpa [prefixWord, tailWord_8047520, baseEnd_8047520] using wordTrace_append hprefix tailTrace_8047520
  have hstable : (prefixWord ++ tailWord_8047520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047520).length < 2 ^ (prefixWord ++ tailWord_8047520).sum := by decide
  have hdescent : baseEnd_8047520 < baseStart_8047520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047524 : List Nat := [2, 3, 1, 2, 1, 2, 3, 2, 3, 2, 2]
def baseStart_8047524 : Nat := 118140960795 + 8047524 * 2 ^ 59
def prefixEnd_8047524 : Nat := 4983230072969 + 3 ^ 40 * 8047524 * 2
def baseEnd_8047524 : Nat := 4132247890593077259040117

theorem tailTrace_8047524 : CollatzResearch.WordTrace tailWord_8047524 prefixEnd_8047524 4132247890593077259040117 := by
  unfold tailWord_8047524
  simp only [CollatzResearch.WordTrace]
  refine ⟨146758656848601215261062813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195678209131468287014750417 146758656848601215261062813)
  ·
    refine ⟨55034496318225455722898555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146758656848601215261062813 55034496318225455722898555)
    ·
      refine ⟨82551744477338183584347833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55034496318225455722898555 82551744477338183584347833)
      ·
        refine ⟨61913808358003637688260875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82551744477338183584347833 61913808358003637688260875)
        ·
          refine ⟨92870712537005456532391313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61913808358003637688260875 92870712537005456532391313)
          ·
            refine ⟨69653034402754092399293485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 92870712537005456532391313 69653034402754092399293485)
            ·
              refine ⟨26119887901032784649735057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 69653034402754092399293485 26119887901032784649735057)
              ·
                refine ⟨19589915925774588487301293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26119887901032784649735057 19589915925774588487301293)
                ·
                  refine ⟨7346218472165470682737985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19589915925774588487301293 7346218472165470682737985)
                  ·
                    refine ⟨5509663854124103012053489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7346218472165470682737985 5509663854124103012053489)
                    ·
                      refine ⟨4132247890593077259040117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5509663854124103012053489 4132247890593077259040117)
                      ·
                        rfl

theorem cell23_8047524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_8047524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047524 prefixEnd_8047524 := by exact prefixLift 8047524
  have htrace : WordTrace (prefixWord ++ tailWord_8047524) baseStart_8047524 baseEnd_8047524 := by
    simpa [prefixWord, tailWord_8047524, baseEnd_8047524] using wordTrace_append hprefix tailTrace_8047524
  have hstable : (prefixWord ++ tailWord_8047524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047524).length < 2 ^ (prefixWord ++ tailWord_8047524).sum := by decide
  have hdescent : baseEnd_8047524 < baseStart_8047524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047544 : List Nat := [2, 1, 2, 1, 2, 4, 4, 1, 1, 2, 3]
def baseStart_8047544 : Nat := 118140960795 + 8047544 * 2 ^ 59
def prefixEnd_8047544 : Nat := 4983230072969 + 3 ^ 40 * 8047544 * 2
def baseEnd_8047544 : Nat := 4132258160206167180790025

theorem tailTrace_8047544 : CollatzResearch.WordTrace tailWord_8047544 prefixEnd_8047544 4132258160206167180790025 := by
  unfold tailWord_8047544
  simp only [CollatzResearch.WordTrace]
  refine ⟨146759021578564986968926843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195678695438086649291902457 146759021578564986968926843)
  ·
    refine ⟨220138532367847480453390265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146759021578564986968926843 220138532367847480453390265)
    ·
      refine ⟨165103899275885610340042699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220138532367847480453390265 165103899275885610340042699)
      ·
        refine ⟨247655848913828415510064049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165103899275885610340042699 247655848913828415510064049)
        ·
          refine ⟨185741886685371311632548037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247655848913828415510064049 185741886685371311632548037)
          ·
            refine ⟨34826603753507120931102757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 185741886685371311632548037 34826603753507120931102757)
            ·
              refine ⟨6529988203782585174581767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 34826603753507120931102757 6529988203782585174581767)
              ·
                refine ⟨9794982305673877761872651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6529988203782585174581767 9794982305673877761872651)
                ·
                  refine ⟨14692473458510816642808977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9794982305673877761872651 14692473458510816642808977)
                  ·
                    refine ⟨11019355093883112482106733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14692473458510816642808977 11019355093883112482106733)
                    ·
                      refine ⟨4132258160206167180790025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11019355093883112482106733 4132258160206167180790025)
                      ·
                        rfl

theorem cell23_8047544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 1, 1, 2, 3].length) (baseStart_8047544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047544 prefixEnd_8047544 := by exact prefixLift 8047544
  have htrace : WordTrace (prefixWord ++ tailWord_8047544) baseStart_8047544 baseEnd_8047544 := by
    simpa [prefixWord, tailWord_8047544, baseEnd_8047544] using wordTrace_append hprefix tailTrace_8047544
  have hstable : (prefixWord ++ tailWord_8047544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047544).length < 2 ^ (prefixWord ++ tailWord_8047544).sum := by decide
  have hdescent : baseEnd_8047544 < baseStart_8047544 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047600 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 3]
def baseStart_8047600 : Nat := 118140960795 + 8047600 * 2 ^ 59
def prefixEnd_8047600 : Nat := 4983230072969 + 3 ^ 40 * 8047600 * 2
def baseEnd_8047600 : Nat := 4132286915122818961689767

theorem tailTrace_8047600 : CollatzResearch.WordTrace tailWord_8047600 prefixEnd_8047600 4132286915122818961689767 := by
  unfold tailWord_8047600
  simp only [CollatzResearch.WordTrace]
  refine ⟨146760042822463547750946127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195680057096618063667928169 146760042822463547750946127)
  ·
    refine ⟨220140064233695321626419191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146760042822463547750946127 220140064233695321626419191)
    ·
      refine ⟨330210096350542982439628787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220140064233695321626419191 330210096350542982439628787)
      ·
        refine ⟨495315144525814473659443181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330210096350542982439628787 495315144525814473659443181)
        ·
          refine ⟨185743179197180427622291193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495315144525814473659443181 185743179197180427622291193)
          ·
            refine ⟨139307384397885320716718395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185743179197180427622291193 139307384397885320716718395)
            ·
              refine ⟨208961076596827981075077593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139307384397885320716718395 208961076596827981075077593)
              ·
                refine ⟨156720807447620985806308195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208961076596827981075077593 156720807447620985806308195)
                ·
                  refine ⟨235081211171431478709462293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156720807447620985806308195 235081211171431478709462293)
                  ·
                    refine ⟨11019431773660850564506045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 235081211171431478709462293 11019431773660850564506045)
                    ·
                      refine ⟨4132286915122818961689767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11019431773660850564506045 4132286915122818961689767)
                      ·
                        rfl

theorem cell23_8047600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 6, 3].length) (baseStart_8047600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047600 prefixEnd_8047600 := by exact prefixLift 8047600
  have htrace : WordTrace (prefixWord ++ tailWord_8047600) baseStart_8047600 baseEnd_8047600 := by
    simpa [prefixWord, tailWord_8047600, baseEnd_8047600] using wordTrace_append hprefix tailTrace_8047600
  have hstable : (prefixWord ++ tailWord_8047600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047600).length < 2 ^ (prefixWord ++ tailWord_8047600).sum := by decide
  have hdescent : baseEnd_8047600 < baseStart_8047600 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047610 : List Nat := [3, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4]
def baseStart_8047610 : Nat := 118140960795 + 8047610 * 2 ^ 59
def prefixEnd_8047610 : Nat := 4983230072969 + 3 ^ 40 * 8047610 * 2
def baseEnd_8047610 : Nat := 4132292049929363922564721

theorem tailTrace_8047610 : CollatzResearch.WordTrace tailWord_8047610 prefixEnd_8047610 4132292049929363922564721 := by
  unfold tailWord_8047610
  simp only [CollatzResearch.WordTrace]
  refine ⟨73380112593722716802439071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195680300249927244806504189 73380112593722716802439071)
  ·
    refine ⟨110070168890584075203658607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73380112593722716802439071 110070168890584075203658607)
    ·
      refine ⟨165105253335876112805487911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110070168890584075203658607 165105253335876112805487911)
      ·
        refine ⟨247657880003814169208231867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165105253335876112805487911 247657880003814169208231867)
        ·
          refine ⟨371486820005721253812347801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247657880003814169208231867 371486820005721253812347801)
          ·
            refine ⟨278615115004290940359260851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371486820005721253812347801 278615115004290940359260851)
            ·
              refine ⟨417922672506436410538891277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278615115004290940359260851 417922672506436410538891277)
              ·
                refine ⟨156721002189913653952084229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 417922672506436410538891277 156721002189913653952084229)
                ·
                  refine ⟨29385187910608810116015793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156721002189913653952084229 29385187910608810116015793)
                  ·
                    refine ⟨22038890932956607587011845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29385187910608810116015793 22038890932956607587011845)
                    ·
                      refine ⟨4132292049929363922564721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22038890932956607587011845 4132292049929363922564721)
                      ·
                        rfl

theorem cell23_8047610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 4, 2, 4].length) (baseStart_8047610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047610 prefixEnd_8047610 := by exact prefixLift 8047610
  have htrace : WordTrace (prefixWord ++ tailWord_8047610) baseStart_8047610 baseEnd_8047610 := by
    simpa [prefixWord, tailWord_8047610, baseEnd_8047610] using wordTrace_append hprefix tailTrace_8047610
  have hstable : (prefixWord ++ tailWord_8047610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047610).length < 2 ^ (prefixWord ++ tailWord_8047610).sum := by decide
  have hdescent : baseEnd_8047610 < baseStart_8047610 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047660 : List Nat := [2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 5]
def baseStart_8047660 : Nat := 118140960795 + 8047660 * 2 ^ 59
def prefixEnd_8047660 : Nat := 4983230072969 + 3 ^ 40 * 8047660 * 2
def baseEnd_8047660 : Nat := 4132317723962088726939491

theorem tailTrace_8047660 : CollatzResearch.WordTrace tailWord_8047660 prefixEnd_8047660 4132317723962088726939491 := by
  unfold tailWord_8047660
  simp only [CollatzResearch.WordTrace]
  refine ⟨146761137012354862874538217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195681516016473150499384289 146761137012354862874538217)
  ·
    refine ⟨110070852759266147155903663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146761137012354862874538217 110070852759266147155903663)
    ·
      refine ⟨165106279138899220733855495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110070852759266147155903663 165106279138899220733855495)
      ·
        refine ⟨247659418708348831100783243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165106279138899220733855495 247659418708348831100783243)
        ·
          refine ⟨371489128062523246651174865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247659418708348831100783243 371489128062523246651174865)
          ·
            refine ⟨278616846046892434988381149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371489128062523246651174865 278616846046892434988381149)
            ·
              refine ⟨104481317267584663120642931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278616846046892434988381149 104481317267584663120642931)
              ·
                refine ⟨156721975901376994680964397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 104481317267584663120642931 156721975901376994680964397)
                ·
                  refine ⟨58770740963016373005361649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 156721975901376994680964397 58770740963016373005361649)
                  ·
                    refine ⟨44078055722262279754021237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58770740963016373005361649 44078055722262279754021237)
                    ·
                      refine ⟨4132317723962088726939491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44078055722262279754021237 4132317723962088726939491)
                      ·
                        rfl

theorem cell23_8047660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_8047660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047660 prefixEnd_8047660 := by exact prefixLift 8047660
  have htrace : WordTrace (prefixWord ++ tailWord_8047660) baseStart_8047660 baseEnd_8047660 := by
    simpa [prefixWord, tailWord_8047660, baseEnd_8047660] using wordTrace_append hprefix tailTrace_8047660
  have hstable : (prefixWord ++ tailWord_8047660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047660).length < 2 ^ (prefixWord ++ tailWord_8047660).sum := by decide
  have hdescent : baseEnd_8047660 < baseStart_8047660 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047677 : List Nat := [1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 5]
def baseStart_8047677 : Nat := 118140960795 + 8047677 * 2 ^ 59
def prefixEnd_8047677 : Nat := 4983230072969 + 3 ^ 40 * 8047677 * 2
def baseEnd_8047677 : Nat := 4132326453133215160426913

theorem tailTrace_8047677 : CollatzResearch.WordTrace tailWord_8047677 prefixEnd_8047677 4132326453133215160426913 := by
  unfold tailWord_8047677
  simp only [CollatzResearch.WordTrace]
  refine ⟨293522894065648137652445285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195681929377098758434963523 293522894065648137652445285)
  ·
    refine ⟨55035542637309025809833491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293522894065648137652445285 55035542637309025809833491)
    ·
      refine ⟨82553313955963538714750237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55035542637309025809833491 82553313955963538714750237)
      ·
        refine ⟨30957492733486327018031339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 82553313955963538714750237 30957492733486327018031339)
        ·
          refine ⟨46436239100229490527047009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30957492733486327018031339 46436239100229490527047009)
          ·
            refine ⟨34827179325172117895285257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46436239100229490527047009 34827179325172117895285257)
            ·
              refine ⟨26120384493879088421463943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34827179325172117895285257 26120384493879088421463943)
              ·
                refine ⟨39180576740818632632195915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26120384493879088421463943 39180576740818632632195915)
                ·
                  refine ⟨58770865111227948948293873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39180576740818632632195915 58770865111227948948293873)
                  ·
                    refine ⟨44078148833420961711220405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58770865111227948948293873 44078148833420961711220405)
                    ·
                      refine ⟨4132326453133215160426913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44078148833420961711220405 4132326453133215160426913)
                      ·
                        rfl

theorem cell23_8047677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_8047677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047677 prefixEnd_8047677 := by exact prefixLift 8047677
  have htrace : WordTrace (prefixWord ++ tailWord_8047677) baseStart_8047677 baseEnd_8047677 := by
    simpa [prefixWord, tailWord_8047677, baseEnd_8047677] using wordTrace_append hprefix tailTrace_8047677
  have hstable : (prefixWord ++ tailWord_8047677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047677).length < 2 ^ (prefixWord ++ tailWord_8047677).sum := by decide
  have hdescent : baseEnd_8047677 < baseStart_8047677 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047697 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 5, 4]
def baseStart_8047697 : Nat := 118140960795 + 8047697 * 2 ^ 59
def prefixEnd_8047697 : Nat := 4983230072969 + 3 ^ 40 * 8047697 * 2
def baseEnd_8047697 : Nat := 1377445574248768360725607

theorem tailTrace_8047697 : CollatzResearch.WordTrace tailWord_8047697 prefixEnd_8047697 1377445574248768360725607 := by
  unfold tailWord_8047697
  simp only [CollatzResearch.WordTrace]
  refine ⟨293523623525575681068173345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195682415683717120712115563 293523623525575681068173345)
  ·
    refine ⟨220142717644181760801130009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293523623525575681068173345 220142717644181760801130009)
    ·
      refine ⟨165107038233136320600847507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220142717644181760801130009 165107038233136320600847507)
      ·
        refine ⟨247660557349704480901271261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165107038233136320600847507 247660557349704480901271261)
        ·
          refine ⟨92872709006139180337976723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 247660557349704480901271261 92872709006139180337976723)
          ·
            refine ⟨139309063509208770506965085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92872709006139180337976723 139309063509208770506965085)
            ·
              refine ⟨52240898815953288940111907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139309063509208770506965085 52240898815953288940111907)
              ·
                refine ⟨78361348223929933410167861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52240898815953288940111907 78361348223929933410167861)
                ·
                  refine ⟨7346376395993431257203237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 78361348223929933410167861 7346376395993431257203237)
                  ·
                    refine ⟨1377445574248768360725607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7346376395993431257203237 1377445574248768360725607)
                    ·
                      rfl

theorem cell23_8047697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_8047697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047697 prefixEnd_8047697 := by exact prefixLift 8047697
  have htrace : WordTrace (prefixWord ++ tailWord_8047697) baseStart_8047697 baseEnd_8047697 := by
    simpa [prefixWord, tailWord_8047697, baseEnd_8047697] using wordTrace_append hprefix tailTrace_8047697
  have hstable : (prefixWord ++ tailWord_8047697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047697).length < 2 ^ (prefixWord ++ tailWord_8047697).sum := by decide
  have hdescent : baseEnd_8047697 < baseStart_8047697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047781 : List Nat := [1, 3, 1, 2, 1, 5, 1, 2, 2, 3, 2]
def baseStart_8047781 : Nat := 118140960795 + 8047781 * 2 ^ 59
def prefixEnd_8047781 : Nat := 4983230072969 + 3 ^ 40 * 8047781 * 2
def baseEnd_8047781 : Nat := 4132379855121282753526435

theorem tailTrace_8047781 : CollatzResearch.WordTrace tailWord_8047781 prefixEnd_8047781 4132379855121282753526435 := by
  unfold tailWord_8047781
  simp only [CollatzResearch.WordTrace]
  refine ⟨293526687257271363414231197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195684458171514242276154131 293526687257271363414231197)
  ·
    refine ⟨110072507721476761280336699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293526687257271363414231197 110072507721476761280336699)
    ·
      refine ⟨165108761582215141920505049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110072507721476761280336699 165108761582215141920505049)
      ·
        refine ⟨123831571186661356440378787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165108761582215141920505049 123831571186661356440378787)
        ·
          refine ⟨185747356779992034660568181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123831571186661356440378787 185747356779992034660568181)
          ·
            refine ⟨17413814698124253249428267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 185747356779992034660568181 17413814698124253249428267)
            ·
              refine ⟨26120722047186379874142401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17413814698124253249428267 26120722047186379874142401)
              ·
                refine ⟨19590541535389784905606801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26120722047186379874142401 19590541535389784905606801)
                ·
                  refine ⟨14692906151542338679205101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19590541535389784905606801 14692906151542338679205101)
                  ·
                    refine ⟨5509839806828377004701913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14692906151542338679205101 5509839806828377004701913)
                    ·
                      refine ⟨4132379855121282753526435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5509839806828377004701913 4132379855121282753526435)
                      ·
                        rfl

theorem cell23_8047781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 3, 2].length) (baseStart_8047781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047781 prefixEnd_8047781 := by exact prefixLift 8047781
  have htrace : WordTrace (prefixWord ++ tailWord_8047781) baseStart_8047781 baseEnd_8047781 := by
    simpa [prefixWord, tailWord_8047781, baseEnd_8047781] using wordTrace_append hprefix tailTrace_8047781
  have hstable : (prefixWord ++ tailWord_8047781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047781).length < 2 ^ (prefixWord ++ tailWord_8047781).sum := by decide
  have hdescent : baseEnd_8047781 < baseStart_8047781 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047807 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 6]
def baseStart_8047807 : Nat := 118140960795 + 8047807 * 2 ^ 59
def prefixEnd_8047807 : Nat := 4983230072969 + 3 ^ 40 * 8047807 * 2
def baseEnd_8047807 : Nat := 4132393205618299651801315

theorem tailTrace_8047807 : CollatzResearch.WordTrace tailWord_8047807 prefixEnd_8047807 4132393205618299651801315 := by
  unfold tailWord_8047807
  simp only [CollatzResearch.WordTrace]
  refine ⟨293527635555177169854677675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195685090370118113236451783 293527635555177169854677675)
  ·
    refine ⟨440291453332765754782016513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293527635555177169854677675 440291453332765754782016513)
    ·
      refine ⟨330218589999574316086512385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440291453332765754782016513 330218589999574316086512385)
      ·
        refine ⟨247663942499680737064884289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330218589999574316086512385 247663942499680737064884289)
        ·
          refine ⟨185747956874760552798663217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247663942499680737064884289 185747956874760552798663217)
          ·
            refine ⟨139310967656070414598997413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185747956874760552798663217 139310967656070414598997413)
            ·
              refine ⟨26120806435513202737312015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139310967656070414598997413 26120806435513202737312015)
              ·
                refine ⟨39181209653269804105968023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26120806435513202737312015 39181209653269804105968023)
                ·
                  refine ⟨58771814479904706158952035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39181209653269804105968023 58771814479904706158952035)
                  ·
                    refine ⟨88157721719857059238428053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 58771814479904706158952035 88157721719857059238428053)
                    ·
                      refine ⟨4132393205618299651801315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 88157721719857059238428053 4132393205618299651801315)
                      ·
                        rfl

theorem cell23_8047807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 1, 6].length) (baseStart_8047807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047807 prefixEnd_8047807 := by exact prefixLift 8047807
  have htrace : WordTrace (prefixWord ++ tailWord_8047807) baseStart_8047807 baseEnd_8047807 := by
    simpa [prefixWord, tailWord_8047807, baseEnd_8047807] using wordTrace_append hprefix tailTrace_8047807
  have hstable : (prefixWord ++ tailWord_8047807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047807).length < 2 ^ (prefixWord ++ tailWord_8047807).sum := by decide
  have hdescent : baseEnd_8047807 < baseStart_8047807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047808 : List Nat := [2, 1, 1, 2, 7, 1, 1, 2, 1, 5]
def baseStart_8047808 : Nat := 118140960795 + 8047808 * 2 ^ 59
def prefixEnd_8047808 : Nat := 4983230072969 + 3 ^ 40 * 8047808 * 2
def baseEnd_8047808 : Nat := 1377464573032984715962937

theorem tailTrace_8047808 : CollatzResearch.WordTrace tailWord_8047808 prefixEnd_8047808 1377464573032984715962937 := by
  unfold tailWord_8047808
  simp only [CollatzResearch.WordTrace]
  refine ⟨146763836014086773512732039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195685114685449031350309385 146763836014086773512732039)
  ·
    refine ⟨220145754021130160269098059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146763836014086773512732039 220145754021130160269098059)
    ·
      refine ⟨330218631031695240403647089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220145754021130160269098059 330218631031695240403647089)
      ·
        refine ⟨247663973273771430302735317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330218631031695240403647089 247663973273771430302735317)
        ·
          refine ⟨5804624373604017897720359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 247663973273771430302735317 5804624373604017897720359)
          ·
            refine ⟨8706936560406026846580539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804624373604017897720359 8706936560406026846580539)
            ·
              refine ⟨13060404840609040269870809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8706936560406026846580539 13060404840609040269870809)
              ·
                refine ⟨9795303630456780202403107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13060404840609040269870809 9795303630456780202403107)
                ·
                  refine ⟨14692955445685170303604661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9795303630456780202403107 14692955445685170303604661)
                  ·
                    refine ⟨1377464573032984715962937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14692955445685170303604661 1377464573032984715962937)
                    ·
                      rfl

theorem cell23_8047808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 7, 1, 1, 2, 1, 5].length) (baseStart_8047808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047808 prefixEnd_8047808 := by exact prefixLift 8047808
  have htrace : WordTrace (prefixWord ++ tailWord_8047808) baseStart_8047808 baseEnd_8047808 := by
    simpa [prefixWord, tailWord_8047808, baseEnd_8047808] using wordTrace_append hprefix tailTrace_8047808
  have hstable : (prefixWord ++ tailWord_8047808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047808).length < 2 ^ (prefixWord ++ tailWord_8047808).sum := by decide
  have hdescent : baseEnd_8047808 < baseStart_8047808 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047857 : List Nat := [1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 5]
def baseStart_8047857 : Nat := 118140960795 + 8047857 * 2 ^ 59
def prefixEnd_8047857 : Nat := 4983230072969 + 3 ^ 40 * 8047857 * 2
def baseEnd_8047857 : Nat := 4132418879651024456176085

theorem tailTrace_8047857 : CollatzResearch.WordTrace tailWord_8047857 prefixEnd_8047857 4132418879651024456176085 := by
  unfold tailWord_8047857
  simp only [CollatzResearch.WordTrace]
  refine ⟨293529459204996028393997825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195686306136664018929331883 293529459204996028393997825)
  ·
    refine ⟨220147094403747021295498369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293529459204996028393997825 220147094403747021295498369)
    ·
      refine ⟨165110320802810265971623777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220147094403747021295498369 165110320802810265971623777)
      ·
        refine ⟨123832740602107699478717833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165110320802810265971623777 123832740602107699478717833)
        ·
          refine ⟨92874555451580774609038375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 123832740602107699478717833 92874555451580774609038375)
          ·
            refine ⟨139311833177371161913557563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92874555451580774609038375 139311833177371161913557563)
            ·
              refine ⟨208967749766056742870336345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139311833177371161913557563 208967749766056742870336345)
              ·
                refine ⟨156725812324542557152752259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208967749766056742870336345 156725812324542557152752259)
                ·
                  refine ⟨235088718486813835729128389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156725812324542557152752259 235088718486813835729128389)
                  ·
                    refine ⟨44079134716277594199211573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 235088718486813835729128389 44079134716277594199211573)
                    ·
                      refine ⟨4132418879651024456176085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44079134716277594199211573 4132418879651024456176085)
                      ·
                        rfl

theorem cell23_8047857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_8047857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047857 prefixEnd_8047857 := by exact prefixLift 8047857
  have htrace : WordTrace (prefixWord ++ tailWord_8047857) baseStart_8047857 baseEnd_8047857 := by
    simpa [prefixWord, tailWord_8047857, baseEnd_8047857] using wordTrace_append hprefix tailTrace_8047857
  have hstable : (prefixWord ++ tailWord_8047857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047857).length < 2 ^ (prefixWord ++ tailWord_8047857).sum := by decide
  have hdescent : baseEnd_8047857 < baseStart_8047857 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047871 : List Nat := [1, 1, 2, 2, 1, 5, 2, 1, 3, 3, 2]
def baseStart_8047871 : Nat := 118140960795 + 8047871 * 2 ^ 59
def prefixEnd_8047871 : Nat := 4983230072969 + 3 ^ 40 * 8047871 * 2
def baseEnd_8047871 : Nat := 4132426068380187401401021

theorem tailTrace_8047871 : CollatzResearch.WordTrace tailWord_8047871 prefixEnd_8047871 4132426068380187401401021 := by
  unfold tailWord_8047871
  simp only [CollatzResearch.WordTrace]
  refine ⟨293529969826945308785007467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195686646551296872523338311 293529969826945308785007467)
  ·
    refine ⟨440294954740417963177511201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293529969826945308785007467 440294954740417963177511201)
    ·
      refine ⟨330221216055313472383133401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440294954740417963177511201 330221216055313472383133401)
      ·
        refine ⟨247665912041485104287350051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 330221216055313472383133401 247665912041485104287350051)
        ·
          refine ⟨371498868062227656431025077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247665912041485104287350051 371498868062227656431025077)
          ·
            refine ⟨34828018880833842790408601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 371498868062227656431025077 34828018880833842790408601)
            ·
              refine ⟨26121014160625382092806451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34828018880833842790408601 26121014160625382092806451)
              ·
                refine ⟨39181521240938073139209677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26121014160625382092806451 39181521240938073139209677)
                ·
                  refine ⟨14693070465351777427203629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39181521240938073139209677 14693070465351777427203629)
                  ·
                    refine ⟨5509901424506916535201361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14693070465351777427203629 5509901424506916535201361)
                    ·
                      refine ⟨4132426068380187401401021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5509901424506916535201361 4132426068380187401401021)
                      ·
                        rfl

theorem cell23_8047871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 3, 2].length) (baseStart_8047871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047871 prefixEnd_8047871 := by exact prefixLift 8047871
  have htrace : WordTrace (prefixWord ++ tailWord_8047871) baseStart_8047871 baseEnd_8047871 := by
    simpa [prefixWord, tailWord_8047871, baseEnd_8047871] using wordTrace_append hprefix tailTrace_8047871
  have hstable : (prefixWord ++ tailWord_8047871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047871).length < 2 ^ (prefixWord ++ tailWord_8047871).sum := by decide
  have hdescent : baseEnd_8047871 < baseStart_8047871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047877 : List Nat := [1, 3, 1, 1, 2, 1, 3, 2, 1, 8]
def baseStart_8047877 : Nat := 118140960795 + 8047877 * 2 ^ 59
def prefixEnd_8047877 : Nat := 4983230072969 + 3 ^ 40 * 8047877 * 2
def baseEnd_8047877 : Nat := 1377476383088038125975331

theorem tailTrace_8047877 : CollatzResearch.WordTrace tailWord_8047877 prefixEnd_8047877 1377476383088038125975331 := by
  unfold tailWord_8047877
  simp only [CollatzResearch.WordTrace]
  refine ⟨293530188664923571809725885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195686792443282381206483923 293530188664923571809725885)
  ·
    refine ⟨110073820749346339428647207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293530188664923571809725885 110073820749346339428647207)
    ·
      refine ⟨165110731124019509142970811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110073820749346339428647207 165110731124019509142970811)
      ·
        refine ⟨247666096686029263714456217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165110731124019509142970811 247666096686029263714456217)
        ·
          refine ⟨185749572514521947785842163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247666096686029263714456217 185749572514521947785842163)
          ·
            refine ⟨278624358771782921678763245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185749572514521947785842163 278624358771782921678763245)
            ·
              refine ⟨104484134539418595629536217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 278624358771782921678763245 104484134539418595629536217)
              ·
                refine ⟨78363100904563946722152163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104484134539418595629536217 78363100904563946722152163)
                ·
                  refine ⟨117544651356845920083228245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78363100904563946722152163 117544651356845920083228245)
                  ·
                    refine ⟨1377476383088038125975331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 117544651356845920083228245 1377476383088038125975331)
                    ·
                      rfl

theorem cell23_8047877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_8047877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047877 prefixEnd_8047877 := by exact prefixLift 8047877
  have htrace : WordTrace (prefixWord ++ tailWord_8047877) baseStart_8047877 baseEnd_8047877 := by
    simpa [prefixWord, tailWord_8047877, baseEnd_8047877] using wordTrace_append hprefix tailTrace_8047877
  have hstable : (prefixWord ++ tailWord_8047877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047877).length < 2 ^ (prefixWord ++ tailWord_8047877).sum := by decide
  have hdescent : baseEnd_8047877 < baseStart_8047877 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8047991 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 4]
def baseStart_8047991 : Nat := 118140960795 + 8047991 * 2 ^ 59
def prefixEnd_8047991 : Nat := 4983230072969 + 3 ^ 40 * 8047991 * 2
def baseEnd_8047991 : Nat := 4132487686058726931900469

theorem tailTrace_8047991 : CollatzResearch.WordTrace tailWord_8047991 prefixEnd_8047991 4132487686058726931900469 := by
  unfold tailWord_8047991
  simp only [CollatzResearch.WordTrace]
  refine ⟨293534346586510569279375827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195689564391007046186250551 293534346586510569279375827)
  ·
    refine ⟨440301519879765853919063741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293534346586510569279375827 440301519879765853919063741)
    ·
      refine ⟨165113069954912195219648903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 440301519879765853919063741 165113069954912195219648903)
      ·
        refine ⟨247669604932368292829473355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165113069954912195219648903 247669604932368292829473355)
        ·
          refine ⟨371504407398552439244210033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247669604932368292829473355 371504407398552439244210033)
          ·
            refine ⟨278628305548914329433157525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371504407398552439244210033 278628305548914329433157525)
            ·
              refine ⟨13060701822605359192179259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 278628305548914329433157525 13060701822605359192179259)
              ·
                refine ⟨19591052733908038788268889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13060701822605359192179259 19591052733908038788268889)
                ·
                  refine ⟨14693289550431029091201667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19591052733908038788268889 14693289550431029091201667)
                  ·
                    refine ⟨22039934325646543636802501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14693289550431029091201667 22039934325646543636802501)
                    ·
                      refine ⟨4132487686058726931900469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22039934325646543636802501 4132487686058726931900469)
                      ·
                        rfl

theorem cell23_8047991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 2, 1, 4].length) (baseStart_8047991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8047991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8047991 prefixEnd_8047991 := by exact prefixLift 8047991
  have htrace : WordTrace (prefixWord ++ tailWord_8047991) baseStart_8047991 baseEnd_8047991 := by
    simpa [prefixWord, tailWord_8047991, baseEnd_8047991] using wordTrace_append hprefix tailTrace_8047991
  have hstable : (prefixWord ++ tailWord_8047991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8047991).length < 2 ^ (prefixWord ++ tailWord_8047991).sum := by decide
  have hdescent : baseEnd_8047991 < baseStart_8047991 := by decide
  rcases family_descends (prefixWord ++ tailWord_8047991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048011 : List Nat := [1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 3]
def baseStart_8048011 : Nat := 118140960795 + 8048011 * 2 ^ 59
def prefixEnd_8048011 : Nat := 4983230072969 + 3 ^ 40 * 8048011 * 2
def baseEnd_8048011 : Nat := 4132497955671816853650377

theorem tailTrace_8048011 : CollatzResearch.WordTrace tailWord_8048011 prefixEnd_8048011 4132497955671816853650377 := by
  unfold tailWord_8048011
  simp only [CollatzResearch.WordTrace]
  refine ⟨293535076046438112695103887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195690050697625408463402591 293535076046438112695103887)
  ·
    refine ⟨440302614069657169042655831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293535076046438112695103887 440302614069657169042655831)
    ·
      refine ⟨660453921104485753563983747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440302614069657169042655831 660453921104485753563983747)
      ·
        refine ⟨990680881656728630345975621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660453921104485753563983747 990680881656728630345975621)
        ·
          refine ⟨185752665310636618189870429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 990680881656728630345975621 185752665310636618189870429)
          ·
            refine ⟨69657249491488731821201411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 185752665310636618189870429 69657249491488731821201411)
            ·
              refine ⟨104485874237233097731802117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 69657249491488731821201411 104485874237233097731802117)
              ·
                refine ⟨19591101419481205824712897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104485874237233097731802117 19591101419481205824712897)
                ·
                  refine ⟨14693326064610904368534673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19591101419481205824712897 14693326064610904368534673)
                  ·
                    refine ⟨11019994548458178276401005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14693326064610904368534673 11019994548458178276401005)
                    ·
                      refine ⟨4132497955671816853650377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11019994548458178276401005 4132497955671816853650377)
                      ·
                        rfl

theorem cell23_8048011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 2, 3].length) (baseStart_8048011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048011 prefixEnd_8048011 := by exact prefixLift 8048011
  have htrace : WordTrace (prefixWord ++ tailWord_8048011) baseStart_8048011 baseEnd_8048011 := by
    simpa [prefixWord, tailWord_8048011, baseEnd_8048011] using wordTrace_append hprefix tailTrace_8048011
  have hstable : (prefixWord ++ tailWord_8048011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048011).length < 2 ^ (prefixWord ++ tailWord_8048011).sum := by decide
  have hdescent : baseEnd_8048011 < baseStart_8048011 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048031 : List Nat := [1, 1, 2, 5, 1, 2, 2, 3, 6]
def baseStart_8048031 : Nat := 118140960795 + 8048031 * 2 ^ 59
def prefixEnd_8048031 : Nat := 4983230072969 + 3 ^ 40 * 8048031 * 2
def baseEnd_8048031 : Nat := 459167580587211863933365

theorem tailTrace_8048031 : CollatzResearch.WordTrace tailWord_8048031 prefixEnd_8048031 459167580587211863933365 := by
  unfold tailWord_8048031
  simp only [CollatzResearch.WordTrace]
  refine ⟨293535805506365656110831947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195690537004243770740554631 293535805506365656110831947)
  ·
    refine ⟨440303708259548484166247921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293535805506365656110831947 440303708259548484166247921)
    ·
      refine ⟨330227781194661363124685941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440303708259548484166247921 330227781194661363124685941)
      ·
        refine ⟨30958854486999502792939307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 330227781194661363124685941 30958854486999502792939307)
        ·
          refine ⟨46438281730499254189408961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30958854486999502792939307 46438281730499254189408961)
          ·
            refine ⟨34828711297874440642056721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46438281730499254189408961 34828711297874440642056721)
            ·
              refine ⟨26121533473405830481542541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34828711297874440642056721 26121533473405830481542541)
              ·
                refine ⟨9795575052527186430578453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26121533473405830481542541 9795575052527186430578453)
                ·
                  refine ⟨459167580587211863933365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9795575052527186430578453 459167580587211863933365)
                  ·
                    rfl

theorem cell23_8048031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 2, 3, 6].length) (baseStart_8048031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048031 prefixEnd_8048031 := by exact prefixLift 8048031
  have htrace : WordTrace (prefixWord ++ tailWord_8048031) baseStart_8048031 baseEnd_8048031 := by
    simpa [prefixWord, tailWord_8048031, baseEnd_8048031] using wordTrace_append hprefix tailTrace_8048031
  have hstable : (prefixWord ++ tailWord_8048031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048031).length < 2 ^ (prefixWord ++ tailWord_8048031).sum := by decide
  have hdescent : baseEnd_8048031 < baseStart_8048031 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048045 : List Nat := [1, 5, 2, 2, 1, 1, 3, 1, 2, 2, 3]
def baseStart_8048045 : Nat := 118140960795 + 8048045 * 2 ^ 59
def prefixEnd_8048045 : Nat := 4983230072969 + 3 ^ 40 * 8048045 * 2
def baseEnd_8048045 : Nat := 4132515414014069720625221

theorem tailTrace_8048045 : CollatzResearch.WordTrace tailWord_8048045 prefixEnd_8048045 4132515414014069720625221 := by
  unfold tailWord_8048045
  simp only [CollatzResearch.WordTrace]
  refine ⟨293536316128314936501841589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195690877418876624334561059 293536316128314936501841589)
  ·
    refine ⟨27519029637029525297047649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293536316128314936501841589 27519029637029525297047649)
    ·
      refine ⟨20639272227772143972785737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27519029637029525297047649 20639272227772143972785737)
      ·
        refine ⟨15479454170829107979589303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20639272227772143972785737 15479454170829107979589303)
        ·
          refine ⟨23219181256243661969383955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15479454170829107979589303 23219181256243661969383955)
          ·
            refine ⟨34828771884365492954075933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23219181256243661969383955 34828771884365492954075933)
            ·
              refine ⟨13060789456637059857778475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 34828771884365492954075933 13060789456637059857778475)
              ·
                refine ⟨19591184184955589786667713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13060789456637059857778475 19591184184955589786667713)
                ·
                  refine ⟨14693388138716692340000785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19591184184955589786667713 14693388138716692340000785)
                  ·
                    refine ⟨11020041104037519255000589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14693388138716692340000785 11020041104037519255000589)
                    ·
                      refine ⟨4132515414014069720625221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11020041104037519255000589 4132515414014069720625221)
                      ·
                        rfl

theorem cell23_8048045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_8048045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048045 prefixEnd_8048045 := by exact prefixLift 8048045
  have htrace : WordTrace (prefixWord ++ tailWord_8048045) baseStart_8048045 baseEnd_8048045 := by
    simpa [prefixWord, tailWord_8048045, baseEnd_8048045] using wordTrace_append hprefix tailTrace_8048045
  have hstable : (prefixWord ++ tailWord_8048045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048045).length < 2 ^ (prefixWord ++ tailWord_8048045).sum := by decide
  have hdescent : baseEnd_8048045 < baseStart_8048045 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048075 : List Nat := [1, 1, 1, 1, 3, 3, 4, 4, 1, 1, 3]
def baseStart_8048075 : Nat := 118140960795 + 8048075 * 2 ^ 59
def prefixEnd_8048075 : Nat := 4983230072969 + 3 ^ 40 * 8048075 * 2
def baseEnd_8048075 : Nat := 4132530818433704603250083

theorem tailTrace_8048075 : CollatzResearch.WordTrace tailWord_8048075 prefixEnd_8048075 4132530818433704603250083 := by
  unfold tailWord_8048075
  simp only [CollatzResearch.WordTrace]
  refine ⟨293537410318206251625433679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195691606878804167750289119 293537410318206251625433679)
  ·
    refine ⟨440306115477309377438150519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293537410318206251625433679 440306115477309377438150519)
    ·
      refine ⟨660459173215964066157225779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440306115477309377438150519 660459173215964066157225779)
      ·
        refine ⟨990688759823946099235838669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660459173215964066157225779 990688759823946099235838669)
        ·
          refine ⟨371508284933979787213439501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 990688759823946099235838669 371508284933979787213439501)
          ·
            refine ⟨139315606850242420205039813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 371508284933979787213439501 139315606850242420205039813)
            ·
              refine ⟨26121676284420453788444965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139315606850242420205039813 26121676284420453788444965)
              ·
                refine ⟨4897814303328835085333431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26121676284420453788444965 4897814303328835085333431)
                ·
                  refine ⟨7346721454993252628000147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4897814303328835085333431 7346721454993252628000147)
                  ·
                    refine ⟨11020082182489878942000221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7346721454993252628000147 11020082182489878942000221)
                    ·
                      refine ⟨4132530818433704603250083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11020082182489878942000221 4132530818433704603250083)
                      ·
                        rfl

theorem cell23_8048075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 4, 1, 1, 3].length) (baseStart_8048075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048075 prefixEnd_8048075 := by exact prefixLift 8048075
  have htrace : WordTrace (prefixWord ++ tailWord_8048075) baseStart_8048075 baseEnd_8048075 := by
    simpa [prefixWord, tailWord_8048075, baseEnd_8048075] using wordTrace_append hprefix tailTrace_8048075
  have hstable : (prefixWord ++ tailWord_8048075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048075).length < 2 ^ (prefixWord ++ tailWord_8048075).sum := by decide
  have hdescent : baseEnd_8048075 < baseStart_8048075 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048111 : List Nat := [1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 4]
def baseStart_8048111 : Nat := 118140960795 + 8048111 * 2 ^ 59
def prefixEnd_8048111 : Nat := 4983230072969 + 3 ^ 40 * 8048111 * 2
def baseEnd_8048111 : Nat := 4132549303737266462399917

theorem tailTrace_8048111 : CollatzResearch.WordTrace tailWord_8048111 prefixEnd_8048111 4132549303737266462399917 := by
  unfold tailWord_8048111
  simp only [CollatzResearch.WordTrace]
  refine ⟨293538723346075829773744187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195692482230717219849162791 293538723346075829773744187)
  ·
    refine ⟨440308085019113744660616281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293538723346075829773744187 440308085019113744660616281)
    ·
      refine ⟨330231063764335308495462211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440308085019113744660616281 330231063764335308495462211)
      ·
        refine ⟨495346595646502962743193317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330231063764335308495462211 495346595646502962743193317)
        ·
          refine ⟨92877486683719305514348747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 495346595646502962743193317 92877486683719305514348747)
          ·
            refine ⟨139316230025578958271523121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92877486683719305514348747 139316230025578958271523121)
            ·
              refine ⟨104487172519184218703642341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139316230025578958271523121 104487172519184218703642341)
              ·
                refine ⟨19591344847347041006932939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 104487172519184218703642341 19591344847347041006932939)
                ·
                  refine ⟨29387017271020561510399409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19591344847347041006932939 29387017271020561510399409)
                  ·
                    refine ⟨22040262953265421132799557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 29387017271020561510399409 22040262953265421132799557)
                    ·
                      refine ⟨4132549303737266462399917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22040262953265421132799557 4132549303737266462399917)
                      ·
                        rfl

theorem cell23_8048111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 1, 2, 4].length) (baseStart_8048111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048111 prefixEnd_8048111 := by exact prefixLift 8048111
  have htrace : WordTrace (prefixWord ++ tailWord_8048111) baseStart_8048111 baseEnd_8048111 := by
    simpa [prefixWord, tailWord_8048111, baseEnd_8048111] using wordTrace_append hprefix tailTrace_8048111
  have hstable : (prefixWord ++ tailWord_8048111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048111).length < 2 ^ (prefixWord ++ tailWord_8048111).sum := by decide
  have hdescent : baseEnd_8048111 < baseStart_8048111 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048118 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_8048118 : Nat := 118140960795 + 8048118 * 2 ^ 59
def prefixEnd_8048118 : Nat := 4983230072969 + 3 ^ 40 * 8048118 * 2
def baseEnd_8048118 : Nat := 4132552898101847935012385

theorem tailTrace_8048118 : CollatzResearch.WordTrace tailWord_8048118 prefixEnd_8048118 4132552898101847935012385 := by
  unfold tailWord_8048118
  simp only [CollatzResearch.WordTrace]
  refine ⟨18346186166065654373078063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195692652438033646646166005 18346186166065654373078063)
  ·
    refine ⟨27519279249098481559617095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18346186166065654373078063 27519279249098481559617095)
    ·
      refine ⟨41278918873647722339425643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27519279249098481559617095 41278918873647722339425643)
      ·
        refine ⟨61918378310471583509138465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41278918873647722339425643 61918378310471583509138465)
        ·
          refine ⟨46438783732853687631853849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 61918378310471583509138465 46438783732853687631853849)
          ·
            refine ⟨34829087799640265723890387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46438783732853687631853849 34829087799640265723890387)
            ·
              refine ⟨52243631699460398585835581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34829087799640265723890387 52243631699460398585835581)
              ·
                refine ⟨19591361887297649469688343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52243631699460398585835581 19591361887297649469688343)
                ·
                  refine ⟨29387042830946474204532515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19591361887297649469688343 29387042830946474204532515)
                  ·
                    refine ⟨44080564246419711306798773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 29387042830946474204532515 44080564246419711306798773)
                    ·
                      refine ⟨4132552898101847935012385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44080564246419711306798773 4132552898101847935012385)
                      ·
                        rfl

theorem cell23_8048118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_8048118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048118 prefixEnd_8048118 := by exact prefixLift 8048118
  have htrace : WordTrace (prefixWord ++ tailWord_8048118) baseStart_8048118 baseEnd_8048118 := by
    simpa [prefixWord, tailWord_8048118, baseEnd_8048118] using wordTrace_append hprefix tailTrace_8048118
  have hstable : (prefixWord ++ tailWord_8048118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048118).length < 2 ^ (prefixWord ++ tailWord_8048118).sum := by decide
  have hdescent : baseEnd_8048118 < baseStart_8048118 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048126 : List Nat := [4, 2, 2, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_8048126 : Nat := 118140960795 + 8048126 * 2 ^ 59
def prefixEnd_8048126 : Nat := 4983230072969 + 3 ^ 40 * 8048126 * 2
def baseEnd_8048126 : Nat := 4132557005947083903712349

theorem tailTrace_8048126 : CollatzResearch.WordTrace tailWord_8048126 prefixEnd_8048126 4132557005947083903712349 := by
  unfold tailWord_8048126
  simp only [CollatzResearch.WordTrace]
  refine ⟨36692408805127685916942529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195692846960680991557026821 36692408805127685916942529)
  ·
    refine ⟨27519306603845764437706897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 36692408805127685916942529 27519306603845764437706897)
    ·
      refine ⟨20639479952884323328280173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 27519306603845764437706897 20639479952884323328280173)
      ·
        refine ⟨7739804982331621248105065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20639479952884323328280173 7739804982331621248105065)
        ·
          refine ⟨5804853736748715936078799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7739804982331621248105065 5804853736748715936078799)
          ·
            refine ⟨8707280605123073904118199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804853736748715936078799 8707280605123073904118199)
            ·
              refine ⟨13060920907684610856177299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707280605123073904118199 13060920907684610856177299)
              ·
                refine ⟨19591381361526916284265949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13060920907684610856177299 19591381361526916284265949)
                ·
                  refine ⟨7346768010572593606599731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19591381361526916284265949 7346768010572593606599731)
                  ·
                    refine ⟨11020152015858890409899597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7346768010572593606599731 11020152015858890409899597)
                    ·
                      refine ⟨4132557005947083903712349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11020152015858890409899597 4132557005947083903712349)
                      ·
                        rfl

theorem cell23_8048126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_8048126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048126 prefixEnd_8048126 := by exact prefixLift 8048126
  have htrace : WordTrace (prefixWord ++ tailWord_8048126) baseStart_8048126 baseEnd_8048126 := by
    simpa [prefixWord, tailWord_8048126, baseEnd_8048126] using wordTrace_append hprefix tailTrace_8048126
  have hstable : (prefixWord ++ tailWord_8048126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048126).length < 2 ^ (prefixWord ++ tailWord_8048126).sum := by decide
  have hdescent : baseEnd_8048126 < baseStart_8048126 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048131 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 3]
def baseStart_8048131 : Nat := 118140960795 + 8048131 * 2 ^ 59
def prefixEnd_8048131 : Nat := 4983230072969 + 3 ^ 40 * 8048131 * 2
def baseEnd_8048131 : Nat := 4132559573350356384149825

theorem tailTrace_8048131 : CollatzResearch.WordTrace tailWord_8048131 prefixEnd_8048131 4132559573350356384149825 := by
  unfold tailWord_8048131
  simp only [CollatzResearch.WordTrace]
  refine ⟨293539452806003373189472247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195692968537335582126314831 293539452806003373189472247)
  ·
    refine ⟨440309179209005059784208371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293539452806003373189472247 440309179209005059784208371)
    ·
      refine ⟨660463768813507589676312557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440309179209005059784208371 660463768813507589676312557)
      ·
        refine ⟨247673913305065346128617209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 660463768813507589676312557 247673913305065346128617209)
        ·
          refine ⟨185755434978799009596462907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247673913305065346128617209 185755434978799009596462907)
          ·
            refine ⟨278633152468198514394694361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185755434978799009596462907 278633152468198514394694361)
            ·
              refine ⟨208974864351148885796020771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278633152468198514394694361 208974864351148885796020771)
              ·
                refine ⟨313462296526723328694031157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208974864351148885796020771 313462296526723328694031157)
                ·
                  refine ⟨29387090299380312065065421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 313462296526723328694031157 29387090299380312065065421)
                  ·
                    refine ⟨11020158862267617024399533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29387090299380312065065421 11020158862267617024399533)
                    ·
                      refine ⟨4132559573350356384149825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11020158862267617024399533 4132559573350356384149825)
                      ·
                        rfl

theorem cell23_8048131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_8048131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048131 prefixEnd_8048131 := by exact prefixLift 8048131
  have htrace : WordTrace (prefixWord ++ tailWord_8048131) baseStart_8048131 baseEnd_8048131 := by
    simpa [prefixWord, tailWord_8048131, baseEnd_8048131] using wordTrace_append hprefix tailTrace_8048131
  have hstable : (prefixWord ++ tailWord_8048131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048131).length < 2 ^ (prefixWord ++ tailWord_8048131).sum := by decide
  have hdescent : baseEnd_8048131 < baseStart_8048131 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048152 : List Nat := [2, 1, 2, 3, 4, 2, 1, 2, 1, 2, 3]
def baseStart_8048152 : Nat := 118140960795 + 8048152 * 2 ^ 59
def prefixEnd_8048152 : Nat := 4983230072969 + 3 ^ 40 * 8048152 * 2
def baseEnd_8048152 : Nat := 4132570356444100801987229

theorem tailTrace_8048152 : CollatzResearch.WordTrace tailWord_8048152 prefixEnd_8048152 4132570356444100801987229 := by
  unfold tailWord_8048152
  simp only [CollatzResearch.WordTrace]
  refine ⟨146770109369463646887993355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195693479159284862517324473 146770109369463646887993355)
  ·
    refine ⟨220155164054195470331990033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146770109369463646887993355 220155164054195470331990033)
    ·
      refine ⟨165116373040646602748992525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220155164054195470331990033 165116373040646602748992525)
      ·
        refine ⟨61918639890242476030872197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 165116373040646602748992525 61918639890242476030872197)
        ·
          refine ⟨11609744979420464255788537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 61918639890242476030872197 11609744979420464255788537)
          ·
            refine ⟨8707308734565348191841403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11609744979420464255788537 8707308734565348191841403)
            ·
              refine ⟨13060963101848022287762105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707308734565348191841403 13060963101848022287762105)
              ·
                refine ⟨9795722326386016715821579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13060963101848022287762105 9795722326386016715821579)
                ·
                  refine ⟨14693583489579025073732369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9795722326386016715821579 14693583489579025073732369)
                  ·
                    refine ⟨11020187617184268805299277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 14693583489579025073732369 11020187617184268805299277)
                    ·
                      refine ⟨4132570356444100801987229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11020187617184268805299277 4132570356444100801987229)
                      ·
                        rfl

theorem cell23_8048152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_8048152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048152 prefixEnd_8048152 := by exact prefixLift 8048152
  have htrace : WordTrace (prefixWord ++ tailWord_8048152) baseStart_8048152 baseEnd_8048152 := by
    simpa [prefixWord, tailWord_8048152, baseEnd_8048152] using wordTrace_append hprefix tailTrace_8048152
  have hstable : (prefixWord ++ tailWord_8048152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048152).length < 2 ^ (prefixWord ++ tailWord_8048152).sum := by decide
  have hdescent : baseEnd_8048152 < baseStart_8048152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048245 : List Nat := [1, 3, 4, 2, 1, 2, 2, 1, 7]
def baseStart_8048245 : Nat := 118140960795 + 8048245 * 2 ^ 59
def prefixEnd_8048245 : Nat := 4983230072969 + 3 ^ 40 * 8048245 * 2
def baseEnd_8048245 : Nat := 459179790016107659791589

theorem tailTrace_8048245 : CollatzResearch.WordTrace tailWord_8048245 prefixEnd_8048245 459179790016107659791589 := by
  unfold tailWord_8048245
  simp only [CollatzResearch.WordTrace]
  refine ⟨293543610727590370659122189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195695740485060247106081459 293543610727590370659122189)
  ·
    refine ⟨110078854022846388997170821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 293543610727590370659122189 110078854022846388997170821)
    ·
      refine ⟨20639785129283697936969529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 110078854022846388997170821 20639785129283697936969529)
      ·
        refine ⟨15479838846962773452727147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20639785129283697936969529 15479838846962773452727147)
        ·
          refine ⟨23219758270444160179090721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15479838846962773452727147 23219758270444160179090721)
          ·
            refine ⟨17414818702833120134318041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23219758270444160179090721 17414818702833120134318041)
            ·
              refine ⟨13061114027124840100738531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17414818702833120134318041 13061114027124840100738531)
              ·
                refine ⟨19591671040687260151107797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13061114027124840100738531 19591671040687260151107797)
                ·
                  refine ⟨459179790016107659791589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19591671040687260151107797 459179790016107659791589)
                  ·
                    rfl

theorem cell23_8048245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 2, 1, 7].length) (baseStart_8048245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048245 prefixEnd_8048245 := by exact prefixLift 8048245
  have htrace : WordTrace (prefixWord ++ tailWord_8048245) baseStart_8048245 baseEnd_8048245 := by
    simpa [prefixWord, tailWord_8048245, baseEnd_8048245] using wordTrace_append hprefix tailTrace_8048245
  have hstable : (prefixWord ++ tailWord_8048245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048245).length < 2 ^ (prefixWord ++ tailWord_8048245).sum := by decide
  have hdescent : baseEnd_8048245 < baseStart_8048245 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048251 : List Nat := [1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 7]
def baseStart_8048251 : Nat := 118140960795 + 8048251 * 2 ^ 59
def prefixEnd_8048251 : Nat := 4983230072969 + 3 ^ 40 * 8048251 * 2
def baseEnd_8048251 : Nat := 4132621191028895914649273

theorem tailTrace_8048251 : CollatzResearch.WordTrace tailWord_8048251 prefixEnd_8048251 4132621191028895914649273 := by
  unfold tailWord_8048251
  simp only [CollatzResearch.WordTrace]
  refine ⟨293543829565568633683840607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195695886377045755789227071 293543829565568633683840607)
  ·
    refine ⟨440315744348352950525760911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293543829565568633683840607 440315744348352950525760911)
    ·
      refine ⟨660473616522529425788641367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440315744348352950525760911 660473616522529425788641367)
      ·
        refine ⟨990710424783794138682962051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660473616522529425788641367 990710424783794138682962051)
        ·
          refine ⟨1486065637175691208024443077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 990710424783794138682962051 1486065637175691208024443077)
          ·
            refine ⟨278637306970442101504583077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1486065637175691208024443077 278637306970442101504583077)
            ·
              refine ⟨52244495056957894032109327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 278637306970442101504583077 52244495056957894032109327)
              ·
                refine ⟨78366742585436841048163991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52244495056957894032109327 78366742585436841048163991)
                ·
                  refine ⟨117550113878155261572245987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78366742585436841048163991 117550113878155261572245987)
                  ·
                    refine ⟨176325170817232892358368981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 117550113878155261572245987 176325170817232892358368981)
                    ·
                      refine ⟨4132621191028895914649273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 176325170817232892358368981 4132621191028895914649273)
                      ·
                        rfl

theorem cell23_8048251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 1, 1, 1, 7].length) (baseStart_8048251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048251 prefixEnd_8048251 := by exact prefixLift 8048251
  have htrace : WordTrace (prefixWord ++ tailWord_8048251) baseStart_8048251 baseEnd_8048251 := by
    simpa [prefixWord, tailWord_8048251, baseEnd_8048251] using wordTrace_append hprefix tailTrace_8048251
  have hstable : (prefixWord ++ tailWord_8048251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048251).length < 2 ^ (prefixWord ++ tailWord_8048251).sum := by decide
  have hdescent : baseEnd_8048251 < baseStart_8048251 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048296 : List Nat := [2, 1, 7, 1, 2, 1, 1, 1, 7]
def baseStart_8048296 : Nat := 118140960795 + 8048296 * 2 ^ 59
def prefixEnd_8048296 : Nat := 4983230072969 + 3 ^ 40 * 8048296 * 2
def baseEnd_8048296 : Nat := 459182699739816470954063

theorem tailTrace_8048296 : CollatzResearch.WordTrace tailWord_8048296 prefixEnd_8048296 459182699739816470954063 := by
  unfold tailWord_8048296
  simp only [CollatzResearch.WordTrace]
  refine ⟨146772735425202803184614371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195696980566937070912819161 146772735425202803184614371)
  ·
    refine ⟨220159103137804204776921557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146772735425202803184614371 220159103137804204776921557)
    ·
      refine ⟨5159978979792286049459099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 220159103137804204776921557 5159978979792286049459099)
      ·
        refine ⟨7739968469688429074188649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5159978979792286049459099 7739968469688429074188649)
        ·
          refine ⟨5804976352266321805641487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7739968469688429074188649 5804976352266321805641487)
          ·
            refine ⟨8707464528399482708462231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5804976352266321805641487 8707464528399482708462231)
            ·
              refine ⟨13061196792599224062693347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8707464528399482708462231 13061196792599224062693347)
              ·
                refine ⟨19591795188898836094040021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13061196792599224062693347 19591795188898836094040021)
                ·
                  refine ⟨459182699739816470954063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 19591795188898836094040021 459182699739816470954063)
                  ·
                    rfl

theorem cell23_8048296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 1, 1, 7].length) (baseStart_8048296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048296 prefixEnd_8048296 := by exact prefixLift 8048296
  have htrace : WordTrace (prefixWord ++ tailWord_8048296) baseStart_8048296 baseEnd_8048296 := by
    simpa [prefixWord, tailWord_8048296, baseEnd_8048296] using wordTrace_append hprefix tailTrace_8048296
  have hstable : (prefixWord ++ tailWord_8048296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048296).length < 2 ^ (prefixWord ++ tailWord_8048296).sum := by decide
  have hdescent : baseEnd_8048296 < baseStart_8048296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048302 : List Nat := [4, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_8048302 : Nat := 118140960795 + 8048302 * 2 ^ 59
def prefixEnd_8048302 : Nat := 4983230072969 + 3 ^ 40 * 8048302 * 2
def baseEnd_8048302 : Nat := 4132647378542275215111539

theorem tailTrace_8048302 : CollatzResearch.WordTrace tailWord_8048302 prefixEnd_8048302 4132647378542275215111539 := by
  unfold tailWord_8048302
  simp only [CollatzResearch.WordTrace]
  refine ⟨36693211211047983674243395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195697126458922579595964773 36693211211047983674243395)
  ·
    refine ⟨55039816816571975511365093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36693211211047983674243395 55039816816571975511365093)
    ·
      refine ⟨10319965653107245408380955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 55039816816571975511365093 10319965653107245408380955)
      ·
        refine ⟨15479948479660868112571433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10319965653107245408380955 15479948479660868112571433)
        ·
          refine ⟨11609961359745651084428575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15479948479660868112571433 11609961359745651084428575)
          ·
            refine ⟨17414942039618476626642863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11609961359745651084428575 17414942039618476626642863)
            ·
              refine ⟨26122413059427714939964295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17414942039618476626642863 26122413059427714939964295)
              ·
                refine ⟨39183619589141572409946443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26122413059427714939964295 39183619589141572409946443)
                ·
                  refine ⟨58775429383712358614919665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 39183619589141572409946443 58775429383712358614919665)
                  ·
                    refine ⟨44081572037784268961189749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 58775429383712358614919665 44081572037784268961189749)
                    ·
                      refine ⟨4132647378542275215111539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44081572037784268961189749 4132647378542275215111539)
                      ·
                        rfl

theorem cell23_8048302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_8048302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048302 prefixEnd_8048302 := by exact prefixLift 8048302
  have htrace : WordTrace (prefixWord ++ tailWord_8048302) baseStart_8048302 baseEnd_8048302 := by
    simpa [prefixWord, tailWord_8048302, baseEnd_8048302] using wordTrace_append hprefix tailTrace_8048302
  have hstable : (prefixWord ++ tailWord_8048302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048302).length < 2 ^ (prefixWord ++ tailWord_8048302).sum := by decide
  have hdescent : baseEnd_8048302 < baseStart_8048302 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048365 : List Nat := [1, 5, 1, 2, 1, 2, 1, 2, 3, 5]
def baseStart_8048365 : Nat := 118140960795 + 8048365 * 2 ^ 59
def prefixEnd_8048365 : Nat := 4983230072969 + 3 ^ 40 * 8048365 * 2
def baseEnd_8048365 : Nat := 1377559909274502822874583

theorem tailTrace_8048365 : CollatzResearch.WordTrace tailWord_8048365 prefixEnd_8048365 1377559909274502822874583 := by
  unfold tailWord_8048365
  simp only [CollatzResearch.WordTrace]
  refine ⟨293547987487155631153490549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195698658324770420768993699 293547987487155631153490549)
  ·
    refine ⟨27520123826920840420639739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 293547987487155631153490549 27520123826920840420639739)
    ·
      refine ⟨41280185740381260630959609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27520123826920840420639739 41280185740381260630959609)
      ·
        refine ⟨30960139305285945473219707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41280185740381260630959609 30960139305285945473219707)
        ·
          refine ⟨46440208957928918209829561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30960139305285945473219707 46440208957928918209829561)
          ·
            refine ⟨34830156718446688657372171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 46440208957928918209829561 34830156718446688657372171)
            ·
              refine ⟨52245235077670032986058257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34830156718446688657372171 52245235077670032986058257)
              ·
                refine ⟨39183926308252524739543693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52245235077670032986058257 39183926308252524739543693)
                ·
                  refine ⟨14693972365594696777328885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39183926308252524739543693 14693972365594696777328885)
                  ·
                    refine ⟨1377559909274502822874583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14693972365594696777328885 1377559909274502822874583)
                    ·
                      rfl

theorem cell23_8048365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 2, 3, 5].length) (baseStart_8048365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048365 prefixEnd_8048365 := by exact prefixLift 8048365
  have htrace : WordTrace (prefixWord ++ tailWord_8048365) baseStart_8048365 baseEnd_8048365 := by
    simpa [prefixWord, tailWord_8048365, baseEnd_8048365] using wordTrace_append hprefix tailTrace_8048365
  have hstable : (prefixWord ++ tailWord_8048365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048365).length < 2 ^ (prefixWord ++ tailWord_8048365).sum := by decide
  have hdescent : baseEnd_8048365 < baseStart_8048365 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048385 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_8048385 : Nat := 118140960795 + 8048385 * 2 ^ 59
def prefixEnd_8048385 : Nat := 4983230072969 + 3 ^ 40 * 8048385 * 2
def baseEnd_8048385 : Nat := 4132689997436598390373657

theorem tailTrace_8048385 : CollatzResearch.WordTrace tailWord_8048385 prefixEnd_8048385 4132689997436598390373657 := by
  unfold tailWord_8048385
  simp only [CollatzResearch.WordTrace]
  refine ⟨293548716947083174569218609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195699144631388783046145739 293548716947083174569218609)
  ·
    refine ⟨220161537710312380926913957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293548716947083174569218609 220161537710312380926913957)
    ·
      refine ⟨41280288320683571423796367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 220161537710312380926913957 41280288320683571423796367)
      ·
        refine ⟨61920432481025357135694551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41280288320683571423796367 61920432481025357135694551)
        ·
          refine ⟨92880648721538035703541827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61920432481025357135694551 92880648721538035703541827)
          ·
            refine ⟨139320973082307053555312741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92880648721538035703541827 139320973082307053555312741)
            ·
              refine ⟨26122682452932572541621139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139320973082307053555312741 26122682452932572541621139)
              ·
                refine ⟨39184023679398858812431709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26122682452932572541621139 39184023679398858812431709)
                ·
                  refine ⟨14694008879774572054661891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39184023679398858812431709 14694008879774572054661891)
                  ·
                    refine ⟨22041013319661858081992837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14694008879774572054661891 22041013319661858081992837)
                    ·
                      refine ⟨4132689997436598390373657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22041013319661858081992837 4132689997436598390373657)
                      ·
                        rfl

theorem cell23_8048385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_8048385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048385 prefixEnd_8048385 := by exact prefixLift 8048385
  have htrace : WordTrace (prefixWord ++ tailWord_8048385) baseStart_8048385 baseEnd_8048385 := by
    simpa [prefixWord, tailWord_8048385, baseEnd_8048385] using wordTrace_append hprefix tailTrace_8048385
  have hstable : (prefixWord ++ tailWord_8048385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048385).length < 2 ^ (prefixWord ++ tailWord_8048385).sum := by decide
  have hdescent : baseEnd_8048385 < baseStart_8048385 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048436 : List Nat := [2, 5, 1, 1, 2, 1, 2, 2, 3, 2, 2]
def baseStart_8048436 : Nat := 118140960795 + 8048436 * 2 ^ 59
def prefixEnd_8048436 : Nat := 4983230072969 + 3 ^ 40 * 8048436 * 2
def baseEnd_8048436 : Nat := 4132716184949977690835923

theorem tailTrace_8048436 : CollatzResearch.WordTrace tailWord_8048436 prefixEnd_8048436 4132716184949977690835923 := by
  unfold tailWord_8048436
  simp only [CollatzResearch.WordTrace]
  refine ⟨146775288534949205139662581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195700384713265606852883441 146775288534949205139662581)
  ·
    refine ⟨13760183300151487981843367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 146775288534949205139662581 13760183300151487981843367)
    ·
      refine ⟨20640274950227231972765051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13760183300151487981843367 20640274950227231972765051)
      ·
        refine ⟨30960412425340847959147577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20640274950227231972765051 30960412425340847959147577)
        ·
          refine ⟨23220309319005635969360683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30960412425340847959147577 23220309319005635969360683)
          ·
            refine ⟨34830463978508453954041025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23220309319005635969360683 34830463978508453954041025)
            ·
              refine ⟨26122847983881340465530769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 34830463978508453954041025 26122847983881340465530769)
              ·
                refine ⟨19592135987911005349148077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26122847983881340465530769 19592135987911005349148077)
                ·
                  refine ⟨7347050995466627005930529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19592135987911005349148077 7347050995466627005930529)
                  ·
                    refine ⟨5510288246599970254447897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7347050995466627005930529 5510288246599970254447897)
                    ·
                      refine ⟨4132716184949977690835923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5510288246599970254447897 4132716184949977690835923)
                      ·
                        rfl

theorem cell23_8048436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 2, 3, 2, 2].length) (baseStart_8048436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048436 prefixEnd_8048436 := by exact prefixLift 8048436
  have htrace : WordTrace (prefixWord ++ tailWord_8048436) baseStart_8048436 baseEnd_8048436 := by
    simpa [prefixWord, tailWord_8048436, baseEnd_8048436] using wordTrace_append hprefix tailTrace_8048436
  have hstable : (prefixWord ++ tailWord_8048436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048436).length < 2 ^ (prefixWord ++ tailWord_8048436).sum := by decide
  have hdescent : baseEnd_8048436 < baseStart_8048436 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048442 : List Nat := [3, 1, 1, 1, 5, 3, 2, 7]
def baseStart_8048442 : Nat := 118140960795 + 8048442 * 2 ^ 59
def prefixEnd_8048442 : Nat := 4983230072969 + 3 ^ 40 * 8048442 * 2
def baseEnd_8048442 : Nat := 153063676512366839531885

theorem tailTrace_8048442 : CollatzResearch.WordTrace tailWord_8048442 prefixEnd_8048442 153063676512366839531885 := by
  unfold tailWord_8048442
  simp only [CollatzResearch.WordTrace]
  refine ⟨73387698976969168326010895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195700530605251115536029053 73387698976969168326010895)
  ·
    refine ⟨110081548465453752489016343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 73387698976969168326010895 110081548465453752489016343)
    ·
      refine ⟨165122322698180628733524515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110081548465453752489016343 165122322698180628733524515)
      ·
        refine ⟨247683484047270943100286773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165122322698180628733524515 247683484047270943100286773)
        ·
          refine ⟨23220326629431650915651885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 247683484047270943100286773 23220326629431650915651885)
          ·
            refine ⟨8707622486036869093369457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23220326629431650915651885 8707622486036869093369457)
            ·
              refine ⟨6530716864527651820027093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8707622486036869093369457 6530716864527651820027093)
              ·
                refine ⟨153063676512366839531885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6530716864527651820027093 153063676512366839531885)
                ·
                  rfl

theorem cell23_8048442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 7].length) (baseStart_8048442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048442 prefixEnd_8048442 := by exact prefixLift 8048442
  have htrace : WordTrace (prefixWord ++ tailWord_8048442) baseStart_8048442 baseEnd_8048442 := by
    simpa [prefixWord, tailWord_8048442, baseEnd_8048442] using wordTrace_append hprefix tailTrace_8048442
  have hstable : (prefixWord ++ tailWord_8048442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048442).length < 2 ^ (prefixWord ++ tailWord_8048442).sum := by decide
  have hdescent : baseEnd_8048442 < baseStart_8048442 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048462 : List Nat := [4, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2]
def baseStart_8048462 : Nat := 118140960795 + 8048462 * 2 ^ 59
def prefixEnd_8048462 : Nat := 4983230072969 + 3 ^ 40 * 8048462 * 2
def baseEnd_8048462 : Nat := 4132729535446994589110803

theorem tailTrace_8048462 : CollatzResearch.WordTrace tailWord_8048462 prefixEnd_8048462 4132729535446994589110803 := by
  unfold tailWord_8048462
  simp only [CollatzResearch.WordTrace]
  refine ⟨36693940670975527089971455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195701016911869477813181093 36693940670975527089971455)
  ·
    refine ⟨55040911006463290634957183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36693940670975527089971455 55040911006463290634957183)
    ·
      refine ⟨82561366509694935952435775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55040911006463290634957183 82561366509694935952435775)
      ·
        refine ⟨123842049764542403928653663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 82561366509694935952435775 123842049764542403928653663)
        ·
          refine ⟨185763074646813605892980495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 123842049764542403928653663 185763074646813605892980495)
          ·
            refine ⟨278644611970220408839470743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185763074646813605892980495 278644611970220408839470743)
            ·
              refine ⟨417966917955330613259206115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278644611970220408839470743 417966917955330613259206115)
              ·
                refine ⟨626950376932995919888809173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417966917955330613259206115 626950376932995919888809173)
                ·
                  refine ⟨14694149459367091872393965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 626950376932995919888809173 14694149459367091872393965)
                  ·
                    refine ⟨5510306047262659452147737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14694149459367091872393965 5510306047262659452147737)
                    ·
                      refine ⟨4132729535446994589110803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5510306047262659452147737 4132729535446994589110803)
                      ·
                        rfl

theorem cell23_8048462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 7, 3, 2].length) (baseStart_8048462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048462 prefixEnd_8048462 := by exact prefixLift 8048462
  have htrace : WordTrace (prefixWord ++ tailWord_8048462) baseStart_8048462 baseEnd_8048462 := by
    simpa [prefixWord, tailWord_8048462, baseEnd_8048462] using wordTrace_append hprefix tailTrace_8048462
  have hstable : (prefixWord ++ tailWord_8048462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048462).length < 2 ^ (prefixWord ++ tailWord_8048462).sum := by decide
  have hdescent : baseEnd_8048462 < baseStart_8048462 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048592 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 3, 4]
def baseStart_8048592 : Nat := 118140960795 + 8048592 * 2 ^ 59
def prefixEnd_8048592 : Nat := 4983230072969 + 3 ^ 40 * 8048592 * 2
def baseEnd_8048592 : Nat := 1377598762644026360161735

theorem tailTrace_8048592 : CollatzResearch.WordTrace tailWord_8048592 prefixEnd_8048592 1377598762644026360161735 := by
  unfold tailWord_8048592
  simp only [CollatzResearch.WordTrace]
  refine ⟨146778133428666624461002015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195704177904888832614669353 146778133428666624461002015)
  ·
    refine ⟨220167200142999936691503023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 146778133428666624461002015 220167200142999936691503023)
    ·
      refine ⟨330250800214499905037254535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220167200142999936691503023 330250800214499905037254535)
      ·
        refine ⟨495376200321749857555881803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330250800214499905037254535 495376200321749857555881803)
        ·
          refine ⟨743064300482624786333822705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495376200321749857555881803 743064300482624786333822705)
          ·
            refine ⟨557298225361968589750367029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 743064300482624786333822705 557298225361968589750367029)
            ·
              refine ⟨52246708627684555289096909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 557298225361968589750367029 52246708627684555289096909)
              ·
                refine ⟨19592515735381708233411341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52246708627684555289096909 19592515735381708233411341)
                ·
                  refine ⟨7347193400768140587529253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 19592515735381708233411341 7347193400768140587529253)
                  ·
                    refine ⟨1377598762644026360161735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7347193400768140587529253 1377598762644026360161735)
                    ·
                      rfl

theorem cell23_8048592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 3, 4].length) (baseStart_8048592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048592 prefixEnd_8048592 := by exact prefixLift 8048592
  have htrace : WordTrace (prefixWord ++ tailWord_8048592) baseStart_8048592 baseEnd_8048592 := by
    simpa [prefixWord, tailWord_8048592, baseEnd_8048592] using wordTrace_append hprefix tailTrace_8048592
  have hstable : (prefixWord ++ tailWord_8048592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048592).length < 2 ^ (prefixWord ++ tailWord_8048592).sum := by decide
  have hdescent : baseEnd_8048592 < baseStart_8048592 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048622 : List Nat := [4, 1, 2, 1, 3, 1, 1, 2, 8]
def baseStart_8048622 : Nat := 118140960795 + 8048622 * 2 ^ 59
def prefixEnd_8048622 : Nat := 4983230072969 + 3 ^ 40 * 8048622 * 2
def baseEnd_8048622 : Nat := 459201299150190440345563

theorem tailTrace_8048622 : CollatzResearch.WordTrace tailWord_8048622 prefixEnd_8048622 459201299150190440345563 := by
  unfold tailWord_8048622
  simp only [CollatzResearch.WordTrace]
  refine ⟨36694670130903070505699515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195704907364816376030397413 36694670130903070505699515)
  ·
    refine ⟨55042005196354605758549273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 36694670130903070505699515 55042005196354605758549273)
    ·
      refine ⟨41281503897265954318911955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55042005196354605758549273 41281503897265954318911955)
      ·
        refine ⟨61922255845898931478367933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41281503897265954318911955 61922255845898931478367933)
        ·
          refine ⟨23220845942212099304387975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 61922255845898931478367933 23220845942212099304387975)
          ·
            refine ⟨34831268913318148956581963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23220845942212099304387975 34831268913318148956581963)
            ·
              refine ⟨52246903369977223434872945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34831268913318148956581963 52246903369977223434872945)
              ·
                refine ⟨39185177527482917576154709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52246903369977223434872945 39185177527482917576154709)
                ·
                  refine ⟨459201299150190440345563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 39185177527482917576154709 459201299150190440345563)
                  ·
                    rfl

theorem cell23_8048622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 1, 1, 2, 8].length) (baseStart_8048622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048622 prefixEnd_8048622 := by exact prefixLift 8048622
  have htrace : WordTrace (prefixWord ++ tailWord_8048622) baseStart_8048622 baseEnd_8048622 := by
    simpa [prefixWord, tailWord_8048622, baseEnd_8048622] using wordTrace_append hprefix tailTrace_8048622
  have hstable : (prefixWord ++ tailWord_8048622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048622).length < 2 ^ (prefixWord ++ tailWord_8048622).sum := by decide
  have hdescent : baseEnd_8048622 < baseStart_8048622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048652 : List Nat := [2, 2, 1, 2, 3, 1, 2, 2, 3, 5]
def baseStart_8048652 : Nat := 118140960795 + 8048652 * 2 ^ 59
def prefixEnd_8048652 : Nat := 4983230072969 + 3 ^ 40 * 8048652 * 2
def baseEnd_8048652 : Nat := 1377609032257116281911643

theorem tailTrace_8048652 : CollatzResearch.WordTrace tailWord_8048652 prefixEnd_8048652 1377609032257116281911643 := by
  unfold tailWord_8048652
  simp only [CollatzResearch.WordTrace]
  refine ⟨146779227618557939584594105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195705636824743919446125473 146779227618557939584594105)
  ·
    refine ⟨110084420713918454688445579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146779227618557939584594105 110084420713918454688445579)
    ·
      refine ⟨165126631070877682032668369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 110084420713918454688445579 165126631070877682032668369)
      ·
        refine ⟨123844973303158261524501277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 165126631070877682032668369 123844973303158261524501277)
        ·
          refine ⟨46441864988684348071687979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 123844973303158261524501277 46441864988684348071687979)
          ·
            refine ⟨69662797483026522107531969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46441864988684348071687979 69662797483026522107531969)
            ·
              refine ⟨52247098112269891580648977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69662797483026522107531969 52247098112269891580648977)
              ·
                refine ⟨39185323584202418685486733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 52247098112269891580648977 39185323584202418685486733)
                ·
                  refine ⟨14694496344075907007057525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39185323584202418685486733 14694496344075907007057525)
                  ·
                    refine ⟨1377609032257116281911643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14694496344075907007057525 1377609032257116281911643)
                    ·
                      rfl

theorem cell23_8048652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 2, 3, 5].length) (baseStart_8048652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048652 prefixEnd_8048652 := by exact prefixLift 8048652
  have htrace : WordTrace (prefixWord ++ tailWord_8048652) baseStart_8048652 baseEnd_8048652 := by
    simpa [prefixWord, tailWord_8048652, baseEnd_8048652] using wordTrace_append hprefix tailTrace_8048652
  have hstable : (prefixWord ++ tailWord_8048652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048652).length < 2 ^ (prefixWord ++ tailWord_8048652).sum := by decide
  have hdescent : baseEnd_8048652 < baseStart_8048652 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048669 : List Nat := [1, 4, 2, 2, 2, 2, 1, 1, 3, 5]
def baseStart_8048669 : Nat := 118140960795 + 8048669 * 2 ^ 59
def prefixEnd_8048669 : Nat := 4983230072969 + 3 ^ 40 * 8048669 * 2
def baseEnd_8048669 : Nat := 1377611941980825093074117

theorem tailTrace_8048669 : CollatzResearch.WordTrace tailWord_8048669 prefixEnd_8048669 1377611941980825093074117 := by
  unfold tailWord_8048669
  simp only [CollatzResearch.WordTrace]
  refine ⟨293559075278054291072557061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195706050185369527381704707 293559075278054291072557061)
  ·
    refine ⟨55042326614635179576104449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293559075278054291072557061 55042326614635179576104449)
    ·
      refine ⟨41281744960976384682078337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55042326614635179576104449 41281744960976384682078337)
      ·
        refine ⟨30961308720732288511558753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41281744960976384682078337 30961308720732288511558753)
        ·
          refine ⟨23220981540549216383669065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30961308720732288511558753 23220981540549216383669065)
          ·
            refine ⟨17415736155411912287751799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23220981540549216383669065 17415736155411912287751799)
            ·
              refine ⟨26123604233117868431627699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17415736155411912287751799 26123604233117868431627699)
              ·
                refine ⟨39185406349676802647441549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26123604233117868431627699 39185406349676802647441549)
                ·
                  refine ⟨14694527381128800992790581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 39185406349676802647441549 14694527381128800992790581)
                  ·
                    refine ⟨1377611941980825093074117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14694527381128800992790581 1377611941980825093074117)
                    ·
                      rfl

theorem cell23_8048669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 1, 3, 5].length) (baseStart_8048669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048669 prefixEnd_8048669 := by exact prefixLift 8048669
  have htrace : WordTrace (prefixWord ++ tailWord_8048669) baseStart_8048669 baseEnd_8048669 := by
    simpa [prefixWord, tailWord_8048669, baseEnd_8048669] using wordTrace_append hprefix tailTrace_8048669
  have hstable : (prefixWord ++ tailWord_8048669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048669).length < 2 ^ (prefixWord ++ tailWord_8048669).sum := by decide
  have hdescent : baseEnd_8048669 < baseStart_8048669 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048734 : List Nat := [4, 4, 1, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_8048734 : Nat := 118140960795 + 8048734 * 2 ^ 59
def prefixEnd_8048734 : Nat := 4983230072969 + 3 ^ 40 * 8048734 * 2
def baseEnd_8048734 : Nat := 4132869202185017524909553

theorem tailTrace_8048734 : CollatzResearch.WordTrace tailWord_8048734 prefixEnd_8048734 4132869202185017524909553 := by
  unfold tailWord_8048734
  simp only [CollatzResearch.WordTrace]
  refine ⟨36695180752852350896709157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 195707630681879204782448837 36695180752852350896709157)
  ·
    refine ⟨6880346391159815793132967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 36695180752852350896709157 6880346391159815793132967)
    ·
      refine ⟨10320519586739723689699451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6880346391159815793132967 10320519586739723689699451)
      ·
        refine ⟨15480779380109585534549177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10320519586739723689699451 15480779380109585534549177)
        ·
          refine ⟨11610584535082189150911883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15480779380109585534549177 11610584535082189150911883)
          ·
            refine ⟨17415876802623283726367825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11610584535082189150911883 17415876802623283726367825)
            ·
              refine ⟨13061907601967462794775869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17415876802623283726367825 13061907601967462794775869)
              ·
                refine ⟨4898215350737798548040951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13061907601967462794775869 4898215350737798548040951)
                ·
                  refine ⟨7347323026106697822061427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4898215350737798548040951 7347323026106697822061427)
                  ·
                    refine ⟨11020984539160046733092141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7347323026106697822061427 11020984539160046733092141)
                    ·
                      refine ⟨4132869202185017524909553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11020984539160046733092141 4132869202185017524909553)
                      ·
                        rfl

theorem cell23_8048734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_8048734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048734 prefixEnd_8048734 := by exact prefixLift 8048734
  have htrace : WordTrace (prefixWord ++ tailWord_8048734) baseStart_8048734 baseEnd_8048734 := by
    simpa [prefixWord, tailWord_8048734, baseEnd_8048734] using wordTrace_append hprefix tailTrace_8048734
  have hstable : (prefixWord ++ tailWord_8048734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048734).length < 2 ^ (prefixWord ++ tailWord_8048734).sum := by decide
  have hdescent : baseEnd_8048734 < baseStart_8048734 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048739 : List Nat := [1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 3]
def baseStart_8048739 : Nat := 118140960795 + 8048739 * 2 ^ 59
def prefixEnd_8048739 : Nat := 4983230072969 + 3 ^ 40 * 8048739 * 2
def baseEnd_8048739 : Nat := 4132871769588290005347029

theorem tailTrace_8048739 : CollatzResearch.WordTrace tailWord_8048739 prefixEnd_8048739 4132871769588290005347029 := by
  unfold tailWord_8048739
  simp only [CollatzResearch.WordTrace]
  refine ⟨293561628387800693027605271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195707752258533795351736847 293561628387800693027605271)
  ·
    refine ⟨440342442581701039541407907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293561628387800693027605271 440342442581701039541407907)
    ·
      refine ⟨660513663872551559312111861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 440342442581701039541407907 660513663872551559312111861)
      ·
        refine ⟨61923155988051708685510487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 660513663872551559312111861 61923155988051708685510487)
        ·
          refine ⟨92884733982077563028265731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61923155988051708685510487 92884733982077563028265731)
          ·
            refine ⟨139327100973116344542398597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92884733982077563028265731 139327100973116344542398597)
            ·
              refine ⟨26123831432459314601699737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 139327100973116344542398597 26123831432459314601699737)
              ·
                refine ⟨19592873574344485951274803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26123831432459314601699737 19592873574344485951274803)
                ·
                  refine ⟨29389310361516728926912205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 19592873574344485951274803 29389310361516728926912205)
                  ·
                    refine ⟨11020991385568773347592077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 29389310361516728926912205 11020991385568773347592077)
                    ·
                      refine ⟨4132871769588290005347029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11020991385568773347592077 4132871769588290005347029)
                      ·
                        rfl

theorem cell23_8048739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_8048739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048739 prefixEnd_8048739 := by exact prefixLift 8048739
  have htrace : WordTrace (prefixWord ++ tailWord_8048739) baseStart_8048739 baseEnd_8048739 := by
    simpa [prefixWord, tailWord_8048739, baseEnd_8048739] using wordTrace_append hprefix tailTrace_8048739
  have hstable : (prefixWord ++ tailWord_8048739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048739).length < 2 ^ (prefixWord ++ tailWord_8048739).sum := by decide
  have hdescent : baseEnd_8048739 < baseStart_8048739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048796 : List Nat := [2, 2, 3, 2, 1, 1, 2, 1, 3, 4, 2]
def baseStart_8048796 : Nat := 118140960795 + 8048796 * 2 ^ 59
def prefixEnd_8048796 : Nat := 4983230072969 + 3 ^ 40 * 8048796 * 2
def baseEnd_8048796 : Nat := 4132901037985596282334267

theorem tailTrace_8048796 : CollatzResearch.WordTrace tailWord_8048796 prefixEnd_8048796 4132901037985596282334267 := by
  unfold tailWord_8048796
  simp only [CollatzResearch.WordTrace]
  refine ⟨146781853674297095881215121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195709138232396127841620161 146781853674297095881215121)
  ·
    refine ⟨110086390255722821910911341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 146781853674297095881215121 110086390255722821910911341)
    ·
      refine ⟨41282396345896058216591753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 110086390255722821910911341 41282396345896058216591753)
      ·
        refine ⟨30961797259422043662443815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41282396345896058216591753 30961797259422043662443815)
        ·
          refine ⟨46442695889133065493665723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 30961797259422043662443815 46442695889133065493665723)
          ·
            refine ⟨69664043833699598240498585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 46442695889133065493665723 69664043833699598240498585)
            ·
              refine ⟨52248032875274698680373939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 69664043833699598240498585 52248032875274698680373939)
              ·
                refine ⟨78372049312912048020560909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52248032875274698680373939 78372049312912048020560909)
                ·
                  refine ⟨29389518492342018007710341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 78372049312912048020560909 29389518492342018007710341)
                  ·
                    refine ⟨5510534717314128376445689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 29389518492342018007710341 5510534717314128376445689)
                    ·
                      refine ⟨4132901037985596282334267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5510534717314128376445689 4132901037985596282334267)
                      ·
                        rfl

theorem cell23_8048796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_8048796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048796 prefixEnd_8048796 := by exact prefixLift 8048796
  have htrace : WordTrace (prefixWord ++ tailWord_8048796) baseStart_8048796 baseEnd_8048796 := by
    simpa [prefixWord, tailWord_8048796, baseEnd_8048796] using wordTrace_append hprefix tailTrace_8048796
  have hstable : (prefixWord ++ tailWord_8048796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048796).length < 2 ^ (prefixWord ++ tailWord_8048796).sum := by decide
  have hdescent : baseEnd_8048796 < baseStart_8048796 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048799 : List Nat := [1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 5]
def baseStart_8048799 : Nat := 118140960795 + 8048799 * 2 ^ 59
def prefixEnd_8048799 : Nat := 4983230072969 + 3 ^ 40 * 8048799 * 2
def baseEnd_8048799 : Nat := 4132902578427559770596753

theorem tailTrace_8048799 : CollatzResearch.WordTrace tailWord_8048799 prefixEnd_8048799 4132902578427559770596753 := by
  unfold tailWord_8048799
  simp only [CollatzResearch.WordTrace]
  refine ⟨293563816767583323274789451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195709211178388882183192967 293563816767583323274789451)
  ·
    refine ⟨440345725151374984912184177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 293563816767583323274789451 440345725151374984912184177)
    ·
      refine ⟨330259293863531238684138133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 440345725151374984912184177 330259293863531238684138133)
      ·
        refine ⟨15480904399853026813318975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 330259293863531238684138133 15480904399853026813318975)
        ·
          refine ⟨23221356599779540219978463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15480904399853026813318975 23221356599779540219978463)
          ·
            refine ⟨34832034899669310329967695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23221356599779540219978463 34832034899669310329967695)
            ·
              refine ⟨52248052349503965494951543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 34832034899669310329967695 52248052349503965494951543)
              ·
                refine ⟨78372078524255948242427315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 52248052349503965494951543 78372078524255948242427315)
                ·
                  refine ⟨117558117786383922363640973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78372078524255948242427315 117558117786383922363640973)
                  ·
                    refine ⟨44084294169893970886365365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 117558117786383922363640973 44084294169893970886365365)
                    ·
                      refine ⟨4132902578427559770596753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 44084294169893970886365365 4132902578427559770596753)
                      ·
                        rfl

theorem cell23_8048799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_8048799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048799 prefixEnd_8048799 := by exact prefixLift 8048799
  have htrace : WordTrace (prefixWord ++ tailWord_8048799) baseStart_8048799 baseEnd_8048799 := by
    simpa [prefixWord, tailWord_8048799, baseEnd_8048799] using wordTrace_append hprefix tailTrace_8048799
  have hstable : (prefixWord ++ tailWord_8048799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048799).length < 2 ^ (prefixWord ++ tailWord_8048799).sum := by decide
  have hdescent : baseEnd_8048799 < baseStart_8048799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048829 : List Nat := [1, 4, 1, 2, 1, 1, 1, 3, 1, 5, 3]
def baseStart_8048829 : Nat := 118140960795 + 8048829 * 2 ^ 59
def prefixEnd_8048829 : Nat := 4983230072969 + 3 ^ 40 * 8048829 * 2
def baseEnd_8048829 : Nat := 4132917982847194653221615

theorem tailTrace_8048829 : CollatzResearch.WordTrace tailWord_8048829 prefixEnd_8048829 4132917982847194653221615 := by
  unfold tailWord_8048829
  simp only [CollatzResearch.WordTrace]
  refine ⟨293564910957474638398381541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195709940638316425598921027 293564910957474638398381541)
  ·
    refine ⟨55043420804526494699696539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 293564910957474638398381541 55043420804526494699696539)
    ·
      refine ⟨82565131206789742049544809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 55043420804526494699696539 82565131206789742049544809)
      ·
        refine ⟨61923848405092306537158607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 82565131206789742049544809 61923848405092306537158607)
        ·
          refine ⟨92885772607638459805737911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61923848405092306537158607 92885772607638459805737911)
          ·
            refine ⟨139328658911457689708606867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92885772607638459805737911 139328658911457689708606867)
            ·
              refine ⟨208992988367186534562910301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 139328658911457689708606867 208992988367186534562910301)
              ·
                refine ⟨78372370637694950461091363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 208992988367186534562910301 78372370637694950461091363)
                ·
                  refine ⟨117558555956542425691637045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 78372370637694950461091363 117558555956542425691637045)
                  ·
                    refine ⟨11021114620925852408590973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 117558555956542425691637045 11021114620925852408590973)
                    ·
                      refine ⟨4132917982847194653221615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11021114620925852408590973 4132917982847194653221615)
                      ·
                        rfl

theorem cell23_8048829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 5, 3].length) (baseStart_8048829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048829 prefixEnd_8048829 := by exact prefixLift 8048829
  have htrace : WordTrace (prefixWord ++ tailWord_8048829) baseStart_8048829 baseEnd_8048829 := by
    simpa [prefixWord, tailWord_8048829, baseEnd_8048829] using wordTrace_append hprefix tailTrace_8048829
  have hstable : (prefixWord ++ tailWord_8048829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048829).length < 2 ^ (prefixWord ++ tailWord_8048829).sum := by decide
  have hdescent : baseEnd_8048829 < baseStart_8048829 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048834 : List Nat := [3, 5, 1, 1, 1, 3, 1, 2, 1, 3, 2]
def baseStart_8048834 : Nat := 118140960795 + 8048834 * 2 ^ 59
def prefixEnd_8048834 : Nat := 4983230072969 + 3 ^ 40 * 8048834 * 2
def baseEnd_8048834 : Nat := 4132920550250467133659093

theorem tailTrace_8048834 : CollatzResearch.WordTrace tailWord_8048834 prefixEnd_8048834 4132920550250467133659093 := by
  unfold tailWord_8048834
  simp only [CollatzResearch.WordTrace]
  refine ⟨73391273330614131063078389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 195710062214971016168209037 73391273330614131063078389)
  ·
    refine ⟨6880431874745074787163599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 73391273330614131063078389 6880431874745074787163599)
    ·
      refine ⟨10320647812117612180745399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6880431874745074787163599 10320647812117612180745399)
      ·
        refine ⟨15480971718176418271118099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10320647812117612180745399 15480971718176418271118099)
        ·
          refine ⟨23221457577264627406677149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15480971718176418271118099 23221457577264627406677149)
          ·
            refine ⟨8708046591474235277503931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23221457577264627406677149 8708046591474235277503931)
            ·
              refine ⟨13062069887211352916255897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708046591474235277503931 13062069887211352916255897)
              ·
                refine ⟨9796552415408514687191923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13062069887211352916255897 9796552415408514687191923)
                ·
                  refine ⟨14694828623112772030787885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9796552415408514687191923 14694828623112772030787885)
                  ·
                    refine ⟨5510560733667289511545457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 14694828623112772030787885 5510560733667289511545457)
                    ·
                      refine ⟨4132920550250467133659093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5510560733667289511545457 4132920550250467133659093)
                      ·
                        rfl

theorem cell23_8048834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_8048834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048834 prefixEnd_8048834 := by exact prefixLift 8048834
  have htrace : WordTrace (prefixWord ++ tailWord_8048834) baseStart_8048834 baseEnd_8048834 := by
    simpa [prefixWord, tailWord_8048834, baseEnd_8048834] using wordTrace_append hprefix tailTrace_8048834
  have hstable : (prefixWord ++ tailWord_8048834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048834).length < 2 ^ (prefixWord ++ tailWord_8048834).sum := by decide
  have hdescent : baseEnd_8048834 < baseStart_8048834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048849 : List Nat := [1, 2, 2, 1, 2, 2, 3, 3, 2, 5]
def baseStart_8048849 : Nat := 118140960795 + 8048849 * 2 ^ 59
def prefixEnd_8048849 : Nat := 4983230072969 + 3 ^ 40 * 8048849 * 2
def baseEnd_8048849 : Nat := 1377642750820094858323841

theorem tailTrace_8048849 : CollatzResearch.WordTrace tailWord_8048849 prefixEnd_8048849 1377642750820094858323841 := by
  unfold tailWord_8048849
  simp only [CollatzResearch.WordTrace]
  refine ⟨293565640417402181814109601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 195710426944934787876073067 293565640417402181814109601)
  ·
    refine ⟨220174230313051636360582201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 293565640417402181814109601 220174230313051636360582201)
    ·
      refine ⟨165130672734788727270436651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 220174230313051636360582201 165130672734788727270436651)
      ·
        refine ⟨247696009102183090905654977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 165130672734788727270436651 247696009102183090905654977)
        ·
          refine ⟨185772006826637318179241233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 247696009102183090905654977 185772006826637318179241233)
          ·
            refine ⟨139329005119977988634430925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 185772006826637318179241233 139329005119977988634430925)
            ·
              refine ⟨52248376919991745737911597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 139329005119977988634430925 52248376919991745737911597)
              ·
                refine ⟨19593141344996904651716849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 52248376919991745737911597 19593141344996904651716849)
                ·
                  refine ⟨14694856008747678488787637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19593141344996904651716849 14694856008747678488787637)
                  ·
                    refine ⟨1377642750820094858323841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14694856008747678488787637 1377642750820094858323841)
                    ·
                      rfl

theorem cell23_8048849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_8048849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048849 prefixEnd_8048849 := by exact prefixLift 8048849
  have htrace : WordTrace (prefixWord ++ tailWord_8048849) baseStart_8048849 baseEnd_8048849 := by
    simpa [prefixWord, tailWord_8048849, baseEnd_8048849] using wordTrace_append hprefix tailTrace_8048849
  have hstable : (prefixWord ++ tailWord_8048849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048849).length < 2 ^ (prefixWord ++ tailWord_8048849).sum := by decide
  have hdescent : baseEnd_8048849 < baseStart_8048849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048886 : List Nat := [5, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_8048886 : Nat := 118140960795 + 8048886 * 2 ^ 59
def prefixEnd_8048886 : Nat := 4983230072969 + 3 ^ 40 * 8048886 * 2
def baseEnd_8048886 : Nat := 4132947251244500930208853

theorem tailTrace_8048886 : CollatzResearch.WordTrace tailWord_8048886 prefixEnd_8048886 4132947251244500930208853 := by
  unfold tailWord_8048886
  simp only [CollatzResearch.WordTrace]
  refine ⟨18347936869891758570825407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 195711326612178758088804341 18347936869891758570825407)
  ·
    refine ⟨27521905304837637856238111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18347936869891758570825407 27521905304837637856238111)
    ·
      refine ⟨41282857957256456784357167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 27521905304837637856238111 41282857957256456784357167)
      ·
        refine ⟨61924286935884685176535751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 41282857957256456784357167 61924286935884685176535751)
        ·
          refine ⟨92886430403827027764803627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 61924286935884685176535751 92886430403827027764803627)
          ·
            refine ⟨139329645605740541647205441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 92886430403827027764803627 139329645605740541647205441)
            ·
              refine ⟨104497234204305406235404081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 139329645605740541647205441 104497234204305406235404081)
              ·
                refine ⟨78372925653229054676553061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 104497234204305406235404081 78372925653229054676553061)
                ·
                  refine ⟨14694923559980447751853699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 78372925653229054676553061 14694923559980447751853699)
                  ·
                    refine ⟨22042385339970671627780549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 14694923559980447751853699 22042385339970671627780549)
                    ·
                      refine ⟨4132947251244500930208853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22042385339970671627780549 4132947251244500930208853)
                      ·
                        rfl

theorem cell23_8048886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_8048886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048886 prefixEnd_8048886 := by exact prefixLift 8048886
  have htrace : WordTrace (prefixWord ++ tailWord_8048886) baseStart_8048886 baseEnd_8048886 := by
    simpa [prefixWord, tailWord_8048886, baseEnd_8048886] using wordTrace_append hprefix tailTrace_8048886
  have hstable : (prefixWord ++ tailWord_8048886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048886).length < 2 ^ (prefixWord ++ tailWord_8048886).sum := by decide
  have hdescent : baseEnd_8048886 < baseStart_8048886 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8048900 : List Nat := [2, 3, 2, 2, 4, 1, 1, 1, 2, 5]
def baseStart_8048900 : Nat := 118140960795 + 8048900 * 2 ^ 59
def prefixEnd_8048900 : Nat := 4983230072969 + 3 ^ 40 * 8048900 * 2
def baseEnd_8048900 : Nat := 1377651479991221291811263

theorem tailTrace_8048900 : CollatzResearch.WordTrace tailWord_8048900 prefixEnd_8048900 1377651479991221291811263 := by
  unfold tailWord_8048900
  simp only [CollatzResearch.WordTrace]
  refine ⟨146783750270108708762108077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 195711667026811611682810769 146783750270108708762108077)
  ·
    refine ⟨55043906351290765785790529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 146783750270108708762108077 55043906351290765785790529)
    ·
      refine ⟨41282929763468074339342897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 55043906351290765785790529 41282929763468074339342897)
      ·
        refine ⟨30962197322601055754507173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 41282929763468074339342897 30962197322601055754507173)
        ·
          refine ⟨5805411997987697953970095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30962197322601055754507173 5805411997987697953970095)
          ·
            refine ⟨8708117996981546930955143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805411997987697953970095 8708117996981546930955143)
            ·
              refine ⟨13062176995472320396432715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8708117996981546930955143 13062176995472320396432715)
              ·
                refine ⟨19593265493208480594649073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13062176995472320396432715 19593265493208480594649073)
                ·
                  refine ⟨14694949119906360445986805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 19593265493208480594649073 14694949119906360445986805)
                  ·
                    refine ⟨1377651479991221291811263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 14694949119906360445986805 1377651479991221291811263)
                    ·
                      rfl

theorem cell23_8048900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 1, 2, 5].length) (baseStart_8048900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8048900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8048900 prefixEnd_8048900 := by exact prefixLift 8048900
  have htrace : WordTrace (prefixWord ++ tailWord_8048900) baseStart_8048900 baseEnd_8048900 := by
    simpa [prefixWord, tailWord_8048900, baseEnd_8048900] using wordTrace_append hprefix tailTrace_8048900
  have hstable : (prefixWord ++ tailWord_8048900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8048900).length < 2 ^ (prefixWord ++ tailWord_8048900).sum := by decide
  have hdescent : baseEnd_8048900 < baseStart_8048900 := by decide
  rcases family_descends (prefixWord ++ tailWord_8048900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
