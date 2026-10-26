import V185TrunkScan23Chunk0429

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2542233 : List Nat := [1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 5]
def baseStart_2542233 : Nat := 118140960795 + 2542233 * 2 ^ 59
def prefixEnd_2542233 : Nat := 4983230072969 + 3 ^ 40 * 2542233 * 2
def baseEnd_2542233 : Nat := 1305387464721657235395989

theorem tailTrace_2542233 : CollatzResearch.WordTrace tailWord_2542233 prefixEnd_2542233 1305387464721657235395989 := by
  unfold tailWord_2542233
  simp only [CollatzResearch.WordTrace]
  refine ⟨92722854998931494674767353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61815236665954329783178235 92722854998931494674767353)
  ·
    refine ⟨69542141249198621006075515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92722854998931494674767353 69542141249198621006075515)
    ·
      refine ⟨104313211873797931509113273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69542141249198621006075515 104313211873797931509113273)
      ·
        refine ⟨78234908905348448631834955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104313211873797931509113273 78234908905348448631834955)
        ·
          refine ⟨117352363358022672947752433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78234908905348448631834955 117352363358022672947752433)
          ·
            refine ⟨88014272518517004710814325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117352363358022672947752433 88014272518517004710814325)
            ·
              refine ⟨8251338048610969191638843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88014272518517004710814325 8251338048610969191638843)
              ·
                refine ⟨12377007072916453787458265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8251338048610969191638843 12377007072916453787458265)
                ·
                  refine ⟨9282755304687340340593699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12377007072916453787458265 9282755304687340340593699)
                  ·
                    refine ⟨13924132957031010510890549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9282755304687340340593699 13924132957031010510890549)
                    ·
                      refine ⟨1305387464721657235395989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13924132957031010510890549 1305387464721657235395989)
                      ·
                        rfl

theorem cell23_2542233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_2542233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542233 prefixEnd_2542233 := by exact prefixLift 2542233
  have htrace : WordTrace (prefixWord ++ tailWord_2542233) baseStart_2542233 baseEnd_2542233 := by
    simpa [prefixWord, tailWord_2542233, baseEnd_2542233] using wordTrace_append hprefix tailTrace_2542233
  have hstable : (prefixWord ++ tailWord_2542233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542233).length < 2 ^ (prefixWord ++ tailWord_2542233).sum := by decide
  have hdescent : baseEnd_2542233 < baseStart_2542233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542243 : List Nat := [1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 4]
def baseStart_2542243 : Nat := 118140960795 + 2542243 * 2 ^ 59
def prefixEnd_2542243 : Nat := 4983230072969 + 3 ^ 40 * 2542243 * 2
def baseEnd_2542243 : Nat := 1305392599528202196270943

theorem tailTrace_2542243 : CollatzResearch.WordTrace tailWord_2542243 prefixEnd_2542243 1305392599528202196270943 := by
  unfold tailWord_2542243
  simp only [CollatzResearch.WordTrace]
  refine ⟨92723219728895266382631383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61815479819263510921754255 92723219728895266382631383)
  ·
    refine ⟨139084829593342899573947075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92723219728895266382631383 139084829593342899573947075)
    ·
      refine ⟨208627244390014349360920613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139084829593342899573947075 208627244390014349360920613)
      ·
        refine ⟨39117608323127690505172615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208627244390014349360920613 39117608323127690505172615)
        ·
          refine ⟨58676412484691535757758923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39117608323127690505172615 58676412484691535757758923)
          ·
            refine ⟨88014618727037303636638385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58676412484691535757758923 88014618727037303636638385)
            ·
              refine ⟨66010964045277977727478789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88014618727037303636638385 66010964045277977727478789)
              ·
                refine ⟨12377055758489620823902273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66010964045277977727478789 12377055758489620823902273)
                ·
                  refine ⟨9282791818867215617926705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12377055758489620823902273 9282791818867215617926705)
                  ·
                    refine ⟨6962093864150411713445029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9282791818867215617926705 6962093864150411713445029)
                    ·
                      refine ⟨1305392599528202196270943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6962093864150411713445029 1305392599528202196270943)
                      ·
                        rfl

theorem cell23_2542243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_2542243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542243 prefixEnd_2542243 := by exact prefixLift 2542243
  have htrace : WordTrace (prefixWord ++ tailWord_2542243) baseStart_2542243 baseEnd_2542243 := by
    simpa [prefixWord, tailWord_2542243, baseEnd_2542243] using wordTrace_append hprefix tailTrace_2542243
  have hstable : (prefixWord ++ tailWord_2542243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542243).length < 2 ^ (prefixWord ++ tailWord_2542243).sum := by decide
  have hdescent : baseEnd_2542243 < baseStart_2542243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542307 : List Nat := [1, 1, 1, 7, 1, 1, 1, 1, 2, 5, 2]
def baseStart_2542307 : Nat := 118140960795 + 2542307 * 2 ^ 59
def prefixEnd_2542307 : Nat := 4983230072969 + 3 ^ 40 * 2542307 * 2
def baseEnd_2542307 : Nat := 1305425462290089945870649

theorem tailTrace_2542307 : CollatzResearch.WordTrace tailWord_2542307 prefixEnd_2542307 1305425462290089945870649 := by
  unfold tailWord_2542307
  simp only [CollatzResearch.WordTrace]
  refine ⟨92725554000663405312961175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61817036000442270208640783 92725554000663405312961175)
  ·
    refine ⟨139088331000995107969441763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92725554000663405312961175 139088331000995107969441763)
    ·
      refine ⟨208632496501492661954162645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139088331000995107969441763 208632496501492661954162645)
      ·
        refine ⟨4889824136753734264550687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 208632496501492661954162645 4889824136753734264550687)
        ·
          refine ⟨7334736205130601396826031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4889824136753734264550687 7334736205130601396826031)
          ·
            refine ⟨11002104307695902095239047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7334736205130601396826031 11002104307695902095239047)
            ·
              refine ⟨16503156461543853142858571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11002104307695902095239047 16503156461543853142858571)
              ·
                refine ⟨24754734692315779714287857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16503156461543853142858571 24754734692315779714287857)
                ·
                  refine ⟨18566051019236834785715893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24754734692315779714287857 18566051019236834785715893)
                  ·
                    refine ⟨1740567283053453261160865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18566051019236834785715893 1740567283053453261160865)
                    ·
                      refine ⟨1305425462290089945870649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1740567283053453261160865 1305425462290089945870649)
                      ·
                        rfl

theorem cell23_2542307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_2542307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542307 prefixEnd_2542307 := by exact prefixLift 2542307
  have htrace : WordTrace (prefixWord ++ tailWord_2542307) baseStart_2542307 baseEnd_2542307 := by
    simpa [prefixWord, tailWord_2542307, baseEnd_2542307] using wordTrace_append hprefix tailTrace_2542307
  have hstable : (prefixWord ++ tailWord_2542307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542307).length < 2 ^ (prefixWord ++ tailWord_2542307).sum := by decide
  have hdescent : baseEnd_2542307 < baseStart_2542307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542330 : List Nat := [3, 1, 1, 1, 1, 3, 3, 1, 5, 4]
def baseStart_2542330 : Nat := 118140960795 + 2542330 * 2 ^ 59
def prefixEnd_2542330 : Nat := 4983230072969 + 3 ^ 40 * 2542330 * 2
def baseEnd_2542330 : Nat := 435145757448381118627681

theorem tailTrace_2542330 : CollatzResearch.WordTrace tailWord_2542330 prefixEnd_2542330 435145757448381118627681 := by
  unfold tailWord_2542330
  simp only [CollatzResearch.WordTrace]
  refine ⟨23181598219895020060262111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61817595253053386827365629 23181598219895020060262111)
  ·
    refine ⟨34772397329842530090393167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23181598219895020060262111 34772397329842530090393167)
    ·
      refine ⟨52158595994763795135589751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34772397329842530090393167 52158595994763795135589751)
      ·
        refine ⟨78237893992145692703384627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52158595994763795135589751 78237893992145692703384627)
        ·
          refine ⟨117356840988218539055076941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78237893992145692703384627 117356840988218539055076941)
          ·
            refine ⟨44008815370581952145653853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117356840988218539055076941 44008815370581952145653853)
            ·
              refine ⟨16503305763968232054620195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44008815370581952145653853 16503305763968232054620195)
              ·
                refine ⟨24754958645952348081930293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16503305763968232054620195 24754958645952348081930293)
                ·
                  refine ⟨2320777373058032632680965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24754958645952348081930293 2320777373058032632680965)
                  ·
                    refine ⟨435145757448381118627681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2320777373058032632680965 435145757448381118627681)
                    ·
                      rfl

theorem cell23_2542330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 5, 4].length) (baseStart_2542330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542330 prefixEnd_2542330 := by exact prefixLift 2542330
  have htrace : WordTrace (prefixWord ++ tailWord_2542330) baseStart_2542330 baseEnd_2542330 := by
    simpa [prefixWord, tailWord_2542330, baseEnd_2542330] using wordTrace_append hprefix tailTrace_2542330
  have hstable : (prefixWord ++ tailWord_2542330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542330).length < 2 ^ (prefixWord ++ tailWord_2542330).sum := by decide
  have hdescent : baseEnd_2542330 < baseStart_2542330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542334 : List Nat := [4, 2, 2, 1, 2, 3, 1, 1, 2, 5]
def baseStart_2542334 : Nat := 118140960795 + 2542334 * 2 ^ 59
def prefixEnd_2542334 : Nat := 4983230072969 + 3 ^ 40 * 2542334 * 2
def baseEnd_2542334 : Nat := 435146442089253780077675

theorem tailTrace_2542334 : CollatzResearch.WordTrace tailWord_2542334 prefixEnd_2542334 435146442089253780077675 := by
  unfold tailWord_2542334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11590817346445698615524257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61817692514377059282796037 11590817346445698615524257)
  ·
    refine ⟨8693113009834273961643193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11590817346445698615524257 8693113009834273961643193)
    ·
      refine ⟨6519834757375705471232395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8693113009834273961643193 6519834757375705471232395)
      ·
        refine ⟨9779752136063558206848593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6519834757375705471232395 9779752136063558206848593)
        ·
          refine ⟨7334814102047668655136445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9779752136063558206848593 7334814102047668655136445)
          ·
            refine ⟨2750555288267875745676167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7334814102047668655136445 2750555288267875745676167)
            ·
              refine ⟨4125832932401813618514251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2750555288267875745676167 4125832932401813618514251)
              ·
                refine ⟨6188749398602720427771377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4125832932401813618514251 6188749398602720427771377)
                ·
                  refine ⟨4641562048952040320828533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6188749398602720427771377 4641562048952040320828533)
                  ·
                    refine ⟨435146442089253780077675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4641562048952040320828533 435146442089253780077675)
                    ·
                      rfl

theorem cell23_2542334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_2542334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542334 prefixEnd_2542334 := by exact prefixLift 2542334
  have htrace : WordTrace (prefixWord ++ tailWord_2542334) baseStart_2542334 baseEnd_2542334 := by
    simpa [prefixWord, tailWord_2542334, baseEnd_2542334] using wordTrace_append hprefix tailTrace_2542334
  have hstable : (prefixWord ++ tailWord_2542334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542334).length < 2 ^ (prefixWord ++ tailWord_2542334).sum := by decide
  have hdescent : baseEnd_2542334 < baseStart_2542334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542364 : List Nat := [2, 2, 3, 1, 1, 3, 2, 4, 1, 4]
def baseStart_2542364 : Nat := 118140960795 + 2542364 * 2 ^ 59
def prefixEnd_2542364 : Nat := 4983230072969 + 3 ^ 40 * 2542364 * 2
def baseEnd_2542364 : Nat := 435151576895798740952629

theorem tailTrace_2542364 : CollatzResearch.WordTrace tailWord_2542364 prefixEnd_2542364 435151576895798740952629 := by
  unfold tailWord_2542364
  simp only [CollatzResearch.WordTrace]
  refine ⟨46363816480728452023893073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61818421974304602698524097 46363816480728452023893073)
  ·
    refine ⟨34772862360546339017919805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46363816480728452023893073 34772862360546339017919805)
    ·
      refine ⟨13039823385204877131719927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34772862360546339017919805 13039823385204877131719927)
      ·
        refine ⟨19559735077807315697579891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13039823385204877131719927 19559735077807315697579891)
        ·
          refine ⟨29339602616710973546369837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19559735077807315697579891 29339602616710973546369837)
          ·
            refine ⟨11002350981266615079888689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29339602616710973546369837 11002350981266615079888689)
            ·
              refine ⟨8251763235949961309916517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11002350981266615079888689 8251763235949961309916517)
              ·
                refine ⟨1547205606740617745609347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8251763235949961309916517 1547205606740617745609347)
                ·
                  refine ⟨2320808410110926618414021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547205606740617745609347 2320808410110926618414021)
                  ·
                    refine ⟨435151576895798740952629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2320808410110926618414021 435151576895798740952629)
                    ·
                      rfl

theorem cell23_2542364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 1, 4].length) (baseStart_2542364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542364 prefixEnd_2542364 := by exact prefixLift 2542364
  have htrace : WordTrace (prefixWord ++ tailWord_2542364) baseStart_2542364 baseEnd_2542364 := by
    simpa [prefixWord, tailWord_2542364, baseEnd_2542364] using wordTrace_append hprefix tailTrace_2542364
  have hstable : (prefixWord ++ tailWord_2542364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542364).length < 2 ^ (prefixWord ++ tailWord_2542364).sum := by decide
  have hdescent : baseEnd_2542364 < baseStart_2542364 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542398 : List Nat := [4, 2, 1, 2, 3, 2, 1, 3, 1, 4]
def baseStart_2542398 : Nat := 118140960795 + 2542398 * 2 ^ 59
def prefixEnd_2542398 : Nat := 4983230072969 + 3 ^ 40 * 2542398 * 2
def baseEnd_2542398 : Nat := 435157396343216363277577

theorem tailTrace_2542398 : CollatzResearch.WordTrace tailWord_2542398 prefixEnd_2542398 435157396343216363277577 := by
  unfold tailWord_2542398
  simp only [CollatzResearch.WordTrace]
  refine ⟨11591109130416715981815481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61819248695555818569682565 11591109130416715981815481)
  ·
    refine ⟨8693331847812536986361611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11591109130416715981815481 8693331847812536986361611)
    ·
      refine ⟨13039997771718805479542417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8693331847812536986361611 13039997771718805479542417)
      ·
        refine ⟨9779998328789104109656813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13039997771718805479542417 9779998328789104109656813)
        ·
          refine ⟨3667499373295914041121305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9779998328789104109656813 3667499373295914041121305)
          ·
            refine ⟨2750624529971935530840979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3667499373295914041121305 2750624529971935530840979)
            ·
              refine ⟨4125936794957903296261469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2750624529971935530840979 4125936794957903296261469)
              ·
                refine ⟨1547226298109213736098051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4125936794957903296261469 1547226298109213736098051)
                ·
                  refine ⟨2320839447163820604147077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547226298109213736098051 2320839447163820604147077)
                  ·
                    refine ⟨435157396343216363277577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2320839447163820604147077 435157396343216363277577)
                    ·
                      rfl

theorem cell23_2542398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_2542398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542398 prefixEnd_2542398 := by exact prefixLift 2542398
  have htrace : WordTrace (prefixWord ++ tailWord_2542398) baseStart_2542398 baseEnd_2542398 := by
    simpa [prefixWord, tailWord_2542398, baseEnd_2542398] using wordTrace_append hprefix tailTrace_2542398
  have hstable : (prefixWord ++ tailWord_2542398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542398).length < 2 ^ (prefixWord ++ tailWord_2542398).sum := by decide
  have hdescent : baseEnd_2542398 < baseStart_2542398 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542444 : List Nat := [2, 2, 1, 1, 4, 1, 2, 1, 5, 2, 2]
def baseStart_2542444 : Nat := 118140960795 + 2542444 * 2 ^ 59
def prefixEnd_2542444 : Nat := 4983230072969 + 3 ^ 40 * 2542444 * 2
def baseEnd_2542444 : Nat := 1305495809139755909857519

theorem tailTrace_2542444 : CollatzResearch.WordTrace tailWord_2542444 prefixEnd_2542444 1305495809139755909857519 := by
  unfold tailWord_2542444
  simp only [CollatzResearch.WordTrace]
  refine ⟨46365275400583538855349193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61820367200778051807132257 46365275400583538855349193)
  ·
    refine ⟨34773956550437654141511895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46365275400583538855349193 34773956550437654141511895)
    ·
      refine ⟨52160934825656481212267843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34773956550437654141511895 52160934825656481212267843)
      ·
        refine ⟨78241402238484721818401765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52160934825656481212267843 78241402238484721818401765)
        ·
          refine ⟨14670262919715885340950331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78241402238484721818401765 14670262919715885340950331)
          ·
            refine ⟨22005394379573828011425497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14670262919715885340950331 22005394379573828011425497)
            ·
              refine ⟨16504045784680371008569123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22005394379573828011425497 16504045784680371008569123)
              ·
                refine ⟨24756068677020556512853685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16504045784680371008569123 24756068677020556512853685)
                ·
                  refine ⟨2320881438470677173080033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24756068677020556512853685 2320881438470677173080033)
                  ·
                    refine ⟨1740661078853007879810025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2320881438470677173080033 1740661078853007879810025)
                    ·
                      refine ⟨1305495809139755909857519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1740661078853007879810025 1305495809139755909857519)
                      ·
                        rfl

theorem cell23_2542444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 5, 2, 2].length) (baseStart_2542444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542444 prefixEnd_2542444 := by exact prefixLift 2542444
  have htrace : WordTrace (prefixWord ++ tailWord_2542444) baseStart_2542444 baseEnd_2542444 := by
    simpa [prefixWord, tailWord_2542444, baseEnd_2542444] using wordTrace_append hprefix tailTrace_2542444
  have hstable : (prefixWord ++ tailWord_2542444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542444).length < 2 ^ (prefixWord ++ tailWord_2542444).sum := by decide
  have hdescent : baseEnd_2542444 < baseStart_2542444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542450 : List Nat := [3, 2, 1, 2, 1, 1, 4, 9]
def baseStart_2542450 : Nat := 118140960795 + 2542450 * 2 ^ 59
def prefixEnd_2542450 : Nat := 4983230072969 + 3 ^ 40 * 2542450 * 2
def baseEnd_2542450 : Nat := 48351810741617884680833

theorem tailTrace_2542450 : CollatzResearch.WordTrace tailWord_2542450 prefixEnd_2542450 48351810741617884680833 := by
  unfold tailWord_2542450
  simp only [CollatzResearch.WordTrace]
  refine ⟨23182692409786335183854201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61820513092763560490277869 23182692409786335183854201)
  ·
    refine ⟨17387019307339751387890651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23182692409786335183854201 17387019307339751387890651)
    ·
      refine ⟨26080528961009627081835977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17387019307339751387890651 26080528961009627081835977)
      ·
        refine ⟨19560396720757220311376983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26080528961009627081835977 19560396720757220311376983)
        ·
          refine ⟨29340595081135830467065475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19560396720757220311376983 29340595081135830467065475)
          ·
            refine ⟨44010892621703745700598213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29340595081135830467065475 44010892621703745700598213)
            ·
              refine ⟨8252042366569452318862165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44010892621703745700598213 8252042366569452318862165)
              ·
                refine ⟨48351810741617884680833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8252042366569452318862165 48351810741617884680833)
                ·
                  rfl

theorem cell23_2542450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 9].length) (baseStart_2542450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542450 prefixEnd_2542450 := by exact prefixLift 2542450
  have htrace : WordTrace (prefixWord ++ tailWord_2542450) baseStart_2542450 baseEnd_2542450 := by
    simpa [prefixWord, tailWord_2542450, baseEnd_2542450] using wordTrace_append hprefix tailTrace_2542450
  have hstable : (prefixWord ++ tailWord_2542450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542450).length < 2 ^ (prefixWord ++ tailWord_2542450).sum := by decide
  have hdescent : baseEnd_2542450 < baseStart_2542450 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542454 : List Nat := [5, 1, 1, 3, 1, 2, 1, 2, 1, 6]
def baseStart_2542454 : Nat := 118140960795 + 2542454 * 2 ^ 59
def prefixEnd_2542454 : Nat := 4983230072969 + 3 ^ 40 * 2542454 * 2
def baseEnd_2542454 : Nat := 435166981315433623577491

theorem tailTrace_2542454 : CollatzResearch.WordTrace tailWord_2542454 prefixEnd_2542454 435166981315433623577491 := by
  unfold tailWord_2542454
  simp only [CollatzResearch.WordTrace]
  refine ⟨5795682220695678088660151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61820610354087232945708277 5795682220695678088660151)
  ·
    refine ⟨8693523331043517132990227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5795682220695678088660151 8693523331043517132990227)
    ·
      refine ⟨13040284996565275699485341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8693523331043517132990227 13040284996565275699485341)
      ·
        refine ⟨4890106873711978387307003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13040284996565275699485341 4890106873711978387307003)
        ·
          refine ⟨7335160310567967580960505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4890106873711978387307003 7335160310567967580960505)
          ·
            refine ⟨5501370232925975685720379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7335160310567967580960505 5501370232925975685720379)
            ·
              refine ⟨8252055349388963528580569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501370232925975685720379 8252055349388963528580569)
              ·
                refine ⟨6189041512041722646435427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8252055349388963528580569 6189041512041722646435427)
                ·
                  refine ⟨9283562268062583969653141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6189041512041722646435427 9283562268062583969653141)
                  ·
                    refine ⟨435166981315433623577491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9283562268062583969653141 435166981315433623577491)
                    ·
                      rfl

theorem cell23_2542454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 6].length) (baseStart_2542454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542454 prefixEnd_2542454 := by exact prefixLift 2542454
  have htrace : WordTrace (prefixWord ++ tailWord_2542454) baseStart_2542454 baseEnd_2542454 := by
    simpa [prefixWord, tailWord_2542454, baseEnd_2542454] using wordTrace_append hprefix tailTrace_2542454
  have hstable : (prefixWord ++ tailWord_2542454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542454).length < 2 ^ (prefixWord ++ tailWord_2542454).sum := by decide
  have hdescent : baseEnd_2542454 < baseStart_2542454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542457 : List Nat := [1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 4]
def baseStart_2542457 : Nat := 118140960795 + 2542457 * 2 ^ 59
def prefixEnd_2542457 : Nat := 4983230072969 + 3 ^ 40 * 2542457 * 2
def baseEnd_2542457 : Nat := 1305502484388264358994959

theorem tailTrace_2542457 : CollatzResearch.WordTrace tailWord_2542457 prefixEnd_2542457 1305502484388264358994959 := by
  unfold tailWord_2542457
  simp only [CollatzResearch.WordTrace]
  refine ⟨92731024950119980930921625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61820683300079987287281083 92731024950119980930921625)
  ·
    refine ⟨69548268712589985698191219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92731024950119980930921625 69548268712589985698191219)
    ·
      refine ⟨104322403068884978547286829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69548268712589985698191219 104322403068884978547286829)
      ·
        refine ⟨39120901150831866955232561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104322403068884978547286829 39120901150831866955232561)
        ·
          refine ⟨29340675863123900216424421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39120901150831866955232561 29340675863123900216424421)
          ·
            refine ⟨5501376724335731290579579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29340675863123900216424421 5501376724335731290579579)
            ·
              refine ⟨8252065086503596935869369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501376724335731290579579 8252065086503596935869369)
              ·
                refine ⟨6189048814877697701902027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8252065086503596935869369 6189048814877697701902027)
                ·
                  refine ⟨9283573222316546552853041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6189048814877697701902027 9283573222316546552853041)
                  ·
                    refine ⟨6962679916737409914639781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9283573222316546552853041 6962679916737409914639781)
                    ·
                      refine ⟨1305502484388264358994959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6962679916737409914639781 1305502484388264358994959)
                      ·
                        rfl

theorem cell23_2542457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_2542457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542457 prefixEnd_2542457 := by exact prefixLift 2542457
  have htrace : WordTrace (prefixWord ++ tailWord_2542457) baseStart_2542457 baseEnd_2542457 := by
    simpa [prefixWord, tailWord_2542457, baseEnd_2542457] using wordTrace_append hprefix tailTrace_2542457
  have hstable : (prefixWord ++ tailWord_2542457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542457).length < 2 ^ (prefixWord ++ tailWord_2542457).sum := by decide
  have hdescent : baseEnd_2542457 < baseStart_2542457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542521 : List Nat := [1, 2, 1, 4, 2, 3, 1, 3, 1, 3, 2]
def baseStart_2542521 : Nat := 118140960795 + 2542521 * 2 ^ 59
def prefixEnd_2542521 : Nat := 4983230072969 + 3 ^ 40 * 2542521 * 2
def baseEnd_2542521 : Nat := 1305535347150152108594665

theorem tailTrace_2542521 : CollatzResearch.WordTrace tailWord_2542521 prefixEnd_2542521 1305535347150152108594665 := by
  unfold tailWord_2542521
  simp only [CollatzResearch.WordTrace]
  refine ⟨92733359221888119861251417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61822239481258746574167611 92733359221888119861251417)
  ·
    refine ⟨69550019416416089895938563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92733359221888119861251417 69550019416416089895938563)
    ·
      refine ⟨104325029124624134843907845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69550019416416089895938563 104325029124624134843907845)
      ·
        refine ⟨19560942960867025283232721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104325029124624134843907845 19560942960867025283232721)
        ·
          refine ⟨14670707220650268962424541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19560942960867025283232721 14670707220650268962424541)
          ·
            refine ⟨5501515207743850860909203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14670707220650268962424541 5501515207743850860909203)
            ·
              refine ⟨8252272811615776291363805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5501515207743850860909203 8252272811615776291363805)
              ·
                refine ⟨3094602304355916109261427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8252272811615776291363805 3094602304355916109261427)
                ·
                  refine ⟨4641903456533874163892141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094602304355916109261427 4641903456533874163892141)
                  ·
                    refine ⟨1740713796200202811459553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4641903456533874163892141 1740713796200202811459553)
                    ·
                      refine ⟨1305535347150152108594665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1740713796200202811459553 1305535347150152108594665)
                      ·
                        rfl

theorem cell23_2542521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 3, 1, 3, 2].length) (baseStart_2542521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542521 prefixEnd_2542521 := by exact prefixLift 2542521
  have htrace : WordTrace (prefixWord ++ tailWord_2542521) baseStart_2542521 baseEnd_2542521 := by
    simpa [prefixWord, tailWord_2542521, baseEnd_2542521] using wordTrace_append hprefix tailTrace_2542521
  have hstable : (prefixWord ++ tailWord_2542521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542521).length < 2 ^ (prefixWord ++ tailWord_2542521).sum := by decide
  have hdescent : baseEnd_2542521 < baseStart_2542521 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542597 : List Nat := [1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 5]
def baseStart_2542597 : Nat := 118140960795 + 2542597 * 2 ^ 59
def prefixEnd_2542597 : Nat := 4983230072969 + 3 ^ 40 * 2542597 * 2
def baseEnd_2542597 : Nat := 1305574371679893811244315

theorem tailTrace_2542597 : CollatzResearch.WordTrace tailWord_2542597 prefixEnd_2542597 1305574371679893811244315 := by
  unfold tailWord_2542597
  simp only [CollatzResearch.WordTrace]
  refine ⟨92736131169612784841018045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61824087446408523227345363 92736131169612784841018045)
  ·
    refine ⟨34776049188604794315381767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92736131169612784841018045 34776049188604794315381767)
    ·
      refine ⟨52164073782907191473072651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34776049188604794315381767 52164073782907191473072651)
      ·
        refine ⟨78246110674360787209608977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52164073782907191473072651 78246110674360787209608977)
        ·
          refine ⟨58684583005770590407206733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78246110674360787209608977 58684583005770590407206733)
          ·
            refine ⟨22006718627163971402702525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58684583005770590407206733 22006718627163971402702525)
            ·
              refine ⟨8252519485186489276013447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22006718627163971402702525 8252519485186489276013447)
              ·
                refine ⟨12378779227779733914020171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8252519485186489276013447 12378779227779733914020171)
                ·
                  refine ⟨18568168841669600871030257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12378779227779733914020171 18568168841669600871030257)
                  ·
                    refine ⟨13926126631252200653272693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18568168841669600871030257 13926126631252200653272693)
                    ·
                      refine ⟨1305574371679893811244315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13926126631252200653272693 1305574371679893811244315)
                      ·
                        rfl

theorem cell23_2542597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 1, 1, 2, 5].length) (baseStart_2542597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542597 prefixEnd_2542597 := by exact prefixLift 2542597
  have htrace : WordTrace (prefixWord ++ tailWord_2542597) baseStart_2542597 baseEnd_2542597 := by
    simpa [prefixWord, tailWord_2542597, baseEnd_2542597] using wordTrace_append hprefix tailTrace_2542597
  have hstable : (prefixWord ++ tailWord_2542597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542597).length < 2 ^ (prefixWord ++ tailWord_2542597).sum := by decide
  have hdescent : baseEnd_2542597 < baseStart_2542597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542621 : List Nat := [1, 4, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_2542621 : Nat := 118140960795 + 2542621 * 2 ^ 59
def prefixEnd_2542621 : Nat := 4983230072969 + 3 ^ 40 * 2542621 * 2
def baseEnd_2542621 : Nat := 435195565071867239114735

theorem tailTrace_2542621 : CollatzResearch.WordTrace tailWord_2542621 prefixEnd_2542621 435195565071867239114735 := by
  unfold tailWord_2542621
  simp only [CollatzResearch.WordTrace]
  refine ⟨92737006521525836939891717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61824671014350557959927811 92737006521525836939891717)
  ·
    refine ⟨17388188722786094426229697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92737006521525836939891717 17388188722786094426229697)
    ·
      refine ⟨13041141542089570819672273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17388188722786094426229697 13041141542089570819672273)
      ·
        refine ⟨9780856156567178114754205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13041141542089570819672273 9780856156567178114754205)
        ·
          refine ⟨3667821058712691793032827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9780856156567178114754205 3667821058712691793032827)
          ·
            refine ⟨5501731588069037689549241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667821058712691793032827 5501731588069037689549241)
            ·
              refine ⟨4126298691051778267161931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5501731588069037689549241 4126298691051778267161931)
              ·
                refine ⟨6189448036577667400742897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126298691051778267161931 6189448036577667400742897)
                ·
                  refine ⟨4642086027433250550557173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6189448036577667400742897 4642086027433250550557173)
                  ·
                    refine ⟨435195565071867239114735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4642086027433250550557173 435195565071867239114735)
                    ·
                      rfl

theorem cell23_2542621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_2542621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542621 prefixEnd_2542621 := by exact prefixLift 2542621
  have htrace : WordTrace (prefixWord ++ tailWord_2542621) baseStart_2542621 baseEnd_2542621 := by
    simpa [prefixWord, tailWord_2542621, baseEnd_2542621] using wordTrace_append hprefix tailTrace_2542621
  have hstable : (prefixWord ++ tailWord_2542621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542621).length < 2 ^ (prefixWord ++ tailWord_2542621).sum := by decide
  have hdescent : baseEnd_2542621 < baseStart_2542621 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542728 : List Nat := [2, 1, 3, 4, 2, 1, 2, 2, 1, 5]
def baseStart_2542728 : Nat := 118140960795 + 2542728 * 2 ^ 59
def prefixEnd_2542728 : Nat := 4983230072969 + 3 ^ 40 * 2542728 * 2
def baseEnd_2542728 : Nat := 435213879215210932902071

theorem tailTrace_2542728 : CollatzResearch.WordTrace tailWord_2542728 prefixEnd_2542728 435213879215210932902071 := by
  unfold tailWord_2542728
  simp only [CollatzResearch.WordTrace]
  refine ⟨46370454566069097107018419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61827272754758796142691225 46370454566069097107018419)
  ·
    refine ⟨69555681849103645660527629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46370454566069097107018419 69555681849103645660527629)
    ·
      refine ⟨26083380693413867122697861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69555681849103645660527629 26083380693413867122697861)
      ·
        refine ⟨4890633880015100085505849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26083380693413867122697861 4890633880015100085505849)
        ·
          refine ⟨3667975410011325064129387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4890633880015100085505849 3667975410011325064129387)
          ·
            refine ⟨5501963115016987596194081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3667975410011325064129387 5501963115016987596194081)
            ·
              refine ⟨4126472336262740697145561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5501963115016987596194081 4126472336262740697145561)
              ·
                refine ⟨3094854252197055522859171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4126472336262740697145561 3094854252197055522859171)
                ·
                  refine ⟨4642281378295583284288757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094854252197055522859171 4642281378295583284288757)
                  ·
                    refine ⟨435213879215210932902071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4642281378295583284288757 435213879215210932902071)
                    ·
                      rfl

theorem cell23_2542728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 2, 1, 5].length) (baseStart_2542728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542728 prefixEnd_2542728 := by exact prefixLift 2542728
  have htrace : WordTrace (prefixWord ++ tailWord_2542728) baseStart_2542728 baseEnd_2542728 := by
    simpa [prefixWord, tailWord_2542728, baseEnd_2542728] using wordTrace_append hprefix tailTrace_2542728
  have hstable : (prefixWord ++ tailWord_2542728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542728).length < 2 ^ (prefixWord ++ tailWord_2542728).sum := by decide
  have hdescent : baseEnd_2542728 < baseStart_2542728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542764 : List Nat := [2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 3]
def baseStart_2542764 : Nat := 118140960795 + 2542764 * 2 ^ 59
def prefixEnd_2542764 : Nat := 4983230072969 + 3 ^ 40 * 2542764 * 2
def baseEnd_2542764 : Nat := 1305660122949194657856047

theorem tailTrace_2542764 : CollatzResearch.WordTrace tailWord_2542764 prefixEnd_2542764 1305660122949194657856047 := by
  unfold tailWord_2542764
  simp only [CollatzResearch.WordTrace]
  refine ⟨46371111080003886181173673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61828148106671848241564897 46371111080003886181173673)
  ·
    refine ⟨34778333310002914635880255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46371111080003886181173673 34778333310002914635880255)
    ·
      refine ⟨52167499965004371953820383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34778333310002914635880255 52167499965004371953820383)
      ·
        refine ⟨78251249947506557930730575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52167499965004371953820383 78251249947506557930730575)
        ·
          refine ⟨117376874921259836896095863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78251249947506557930730575 117376874921259836896095863)
          ·
            refine ⟨176065312381889755344143795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117376874921259836896095863 176065312381889755344143795)
            ·
              refine ⟨264097968572834633016215693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176065312381889755344143795 264097968572834633016215693)
              ·
                refine ⟨99036738214812987381080885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264097968572834633016215693 99036738214812987381080885)
                ·
                  refine ⟨9284694207638717566976333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99036738214812987381080885 9284694207638717566976333)
                  ·
                    refine ⟨3481760327864519087616125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9284694207638717566976333 3481760327864519087616125)
                    ·
                      refine ⟨1305660122949194657856047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3481760327864519087616125 1305660122949194657856047)
                      ·
                        rfl

theorem cell23_2542764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_2542764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542764 prefixEnd_2542764 := by exact prefixLift 2542764
  have htrace : WordTrace (prefixWord ++ tailWord_2542764) baseStart_2542764 baseEnd_2542764 := by
    simpa [prefixWord, tailWord_2542764, baseEnd_2542764] using wordTrace_append hprefix tailTrace_2542764
  have hstable : (prefixWord ++ tailWord_2542764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542764).length < 2 ^ (prefixWord ++ tailWord_2542764).sum := by decide
  have hdescent : baseEnd_2542764 < baseStart_2542764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542785 : List Nat := [1, 2, 6, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_2542785 : Nat := 118140960795 + 2542785 * 2 ^ 59
def prefixEnd_2542785 : Nat := 4983230072969 + 3 ^ 40 * 2542785 * 2
def baseEnd_2542785 : Nat := 1305670906042939075693451

theorem tailTrace_2542785 : CollatzResearch.WordTrace tailWord_2542785 prefixEnd_2542785 1305670906042939075693451 := by
  unfold tailWord_2542785
  simp only [CollatzResearch.WordTrace]
  refine ⟨92742988092931692948861809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61828658728621128632574539 92742988092931692948861809)
  ·
    refine ⟨69557241069698769711646357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92742988092931692948861809 69557241069698769711646357)
    ·
      refine ⟨3260495675142129830233423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 69557241069698769711646357 3260495675142129830233423)
      ·
        refine ⟨4890743512713194745350135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3260495675142129830233423 4890743512713194745350135)
        ·
          refine ⟨7336115269069792118025203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4890743512713194745350135 7336115269069792118025203)
          ·
            refine ⟨11004172903604688177037805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7336115269069792118025203 11004172903604688177037805)
            ·
              refine ⟨4126564838851758066389177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11004172903604688177037805 4126564838851758066389177)
              ·
                refine ⟨3094923629138818549791883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4126564838851758066389177 3094923629138818549791883)
                ·
                  refine ⟨4642385443708227824687825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3094923629138818549791883 4642385443708227824687825)
                  ·
                    refine ⟨3481789082781170868515869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4642385443708227824687825 3481789082781170868515869)
                    ·
                      refine ⟨1305670906042939075693451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3481789082781170868515869 1305670906042939075693451)
                      ·
                        rfl

theorem cell23_2542785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_2542785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542785 prefixEnd_2542785 := by exact prefixLift 2542785
  have htrace : WordTrace (prefixWord ++ tailWord_2542785) baseStart_2542785 baseEnd_2542785 := by
    simpa [prefixWord, tailWord_2542785, baseEnd_2542785] using wordTrace_append hprefix tailTrace_2542785
  have hstable : (prefixWord ++ tailWord_2542785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542785).length < 2 ^ (prefixWord ++ tailWord_2542785).sum := by decide
  have hdescent : baseEnd_2542785 < baseStart_2542785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542798 : List Nat := [4, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_2542798 : Nat := 118140960795 + 2542798 * 2 ^ 59
def prefixEnd_2542798 : Nat := 4983230072969 + 3 ^ 40 * 2542798 * 2
def baseEnd_2542798 : Nat := 1305677581291447524830891

theorem tailTrace_2542798 : CollatzResearch.WordTrace tailWord_2542798 prefixEnd_2542798 1305677581291447524830891 := by
  unfold tailWord_2542798
  simp only [CollatzResearch.WordTrace]
  refine ⟨11592932780235574521135631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61828974827923064112723365 11592932780235574521135631)
  ·
    refine ⟨17389399170353361781703447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11592932780235574521135631 17389399170353361781703447)
    ·
      refine ⟨26084098755530042672555171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17389399170353361781703447 26084098755530042672555171)
      ·
        refine ⟨39126148133295064008832757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26084098755530042672555171 39126148133295064008832757)
        ·
          refine ⟨3668076387496412250828071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39126148133295064008832757 3668076387496412250828071)
          ·
            refine ⟨5502114581244618376242107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3668076387496412250828071 5502114581244618376242107)
            ·
              refine ⟨8253171871866927564363161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5502114581244618376242107 8253171871866927564363161)
              ·
                refine ⟨6189878903900195673272371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8253171871866927564363161 6189878903900195673272371)
                ·
                  refine ⟨9284818355850293509908557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6189878903900195673272371 9284818355850293509908557)
                  ·
                    refine ⟨3481806883443860066215709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9284818355850293509908557 3481806883443860066215709)
                    ·
                      refine ⟨1305677581291447524830891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3481806883443860066215709 1305677581291447524830891)
                      ·
                        rfl

theorem cell23_2542798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_2542798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542798 prefixEnd_2542798 := by exact prefixLift 2542798
  have htrace : WordTrace (prefixWord ++ tailWord_2542798) baseStart_2542798 baseEnd_2542798 := by
    simpa [prefixWord, tailWord_2542798, baseEnd_2542798] using wordTrace_append hprefix tailTrace_2542798
  have hstable : (prefixWord ++ tailWord_2542798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542798).length < 2 ^ (prefixWord ++ tailWord_2542798).sum := by decide
  have hdescent : baseEnd_2542798 < baseStart_2542798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542831 : List Nat := [1, 1, 2, 1, 7, 1, 1, 1, 2, 6]
def baseStart_2542831 : Nat := 118140960795 + 2542831 * 2 ^ 59
def prefixEnd_2542831 : Nat := 4983230072969 + 3 ^ 40 * 2542831 * 2
def baseEnd_2542831 : Nat := 435231508717681965239413

theorem tailTrace_2542831 : CollatzResearch.WordTrace tailWord_2542831 prefixEnd_2542831 435231508717681965239413 := by
  unfold tailWord_2542831
  simp only [CollatzResearch.WordTrace]
  refine ⟨92744665850765042805036347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61829777233843361870024231 92744665850765042805036347)
  ·
    refine ⟨139116998776147564207554521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92744665850765042805036347 139116998776147564207554521)
    ·
      refine ⟨104337749082110673155665891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139116998776147564207554521 104337749082110673155665891)
      ·
        refine ⟨156506623623166009733498837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104337749082110673155665891 156506623623166009733498837)
        ·
          refine ⟨3668123991167953353128879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 156506623623166009733498837 3668123991167953353128879)
          ·
            refine ⟨5502185986751930029693319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3668123991167953353128879 5502185986751930029693319)
            ·
              refine ⟨8253278980127895044539979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5502185986751930029693319 8253278980127895044539979)
              ·
                refine ⟨12379918470191842566809969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8253278980127895044539979 12379918470191842566809969)
                ·
                  refine ⟨9284938852643881925107477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12379918470191842566809969 9284938852643881925107477)
                  ·
                    refine ⟨435231508717681965239413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9284938852643881925107477 435231508717681965239413)
                    ·
                      rfl

theorem cell23_2542831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 1, 1, 1, 2, 6].length) (baseStart_2542831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542831 prefixEnd_2542831 := by exact prefixLift 2542831
  have htrace : WordTrace (prefixWord ++ tailWord_2542831) baseStart_2542831 baseEnd_2542831 := by
    simpa [prefixWord, tailWord_2542831, baseEnd_2542831] using wordTrace_append hprefix tailTrace_2542831
  have hstable : (prefixWord ++ tailWord_2542831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542831).length < 2 ^ (prefixWord ++ tailWord_2542831).sum := by decide
  have hdescent : baseEnd_2542831 < baseStart_2542831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542866 : List Nat := [3, 2, 4, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2542866 : Nat := 118140960795 + 2542866 * 2 ^ 59
def prefixEnd_2542866 : Nat := 4983230072969 + 3 ^ 40 * 2542866 * 2
def baseEnd_2542866 : Nat := 1305712497975953258780579

theorem tailTrace_2542866 : CollatzResearch.WordTrace tailWord_2542866 prefixEnd_2542866 1305712497975953258780579 := by
  unfold tailWord_2542866
  simp only [CollatzResearch.WordTrace]
  refine ⟨23186485601409560945640113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61830628270425495855040301 23186485601409560945640113)
  ·
    refine ⟨17389864201057170709230085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23186485601409560945640113 17389864201057170709230085)
    ·
      refine ⟨3260599537698219507980641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17389864201057170709230085 3260599537698219507980641)
      ·
        refine ⟨2445449653273664630985481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3260599537698219507980641 2445449653273664630985481)
        ·
          refine ⟨1834087239955248473239111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2445449653273664630985481 1834087239955248473239111)
          ·
            refine ⟨2751130859932872709858667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834087239955248473239111 2751130859932872709858667)
            ·
              refine ⟨4126696289899309064788001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751130859932872709858667 4126696289899309064788001)
              ·
                refine ⟨3095022217424481798591001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4126696289899309064788001 3095022217424481798591001)
                ·
                  refine ⟨2321266663068361348943251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3095022217424481798591001 2321266663068361348943251)
                  ·
                    refine ⟨3481899994602542023414877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2321266663068361348943251 3481899994602542023414877)
                    ·
                      refine ⟨1305712497975953258780579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3481899994602542023414877 1305712497975953258780579)
                      ·
                        rfl

theorem cell23_2542866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2542866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542866 prefixEnd_2542866 := by exact prefixLift 2542866
  have htrace : WordTrace (prefixWord ++ tailWord_2542866) baseStart_2542866 baseEnd_2542866 := by
    simpa [prefixWord, tailWord_2542866, baseEnd_2542866] using wordTrace_append hprefix tailTrace_2542866
  have hstable : (prefixWord ++ tailWord_2542866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542866).length < 2 ^ (prefixWord ++ tailWord_2542866).sum := by decide
  have hdescent : baseEnd_2542866 < baseStart_2542866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542871 : List Nat := [1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 3]
def baseStart_2542871 : Nat := 118140960795 + 2542871 * 2 ^ 59
def prefixEnd_2542871 : Nat := 4983230072969 + 3 ^ 40 * 2542871 * 2
def baseEnd_2542871 : Nat := 1305715065379225739218055

theorem tailTrace_2542871 : CollatzResearch.WordTrace tailWord_2542871 prefixEnd_2542871 1305715065379225739218055 := by
  unfold tailWord_2542871
  simp only [CollatzResearch.WordTrace]
  refine ⟨92746124770620129636492467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61830749847080086424328311 92746124770620129636492467)
  ·
    refine ⟨139119187155930194454738701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92746124770620129636492467 139119187155930194454738701)
    ·
      refine ⟨52169695183473822920527013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139119187155930194454738701 52169695183473822920527013)
      ·
        refine ⟨9781817846901341797598815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52169695183473822920527013 9781817846901341797598815)
        ·
          refine ⟨14672726770352012696398223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9781817846901341797598815 14672726770352012696398223)
          ·
            refine ⟨22009090155528019044597335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14672726770352012696398223 22009090155528019044597335)
            ·
              refine ⟨33013635233292028566896003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22009090155528019044597335 33013635233292028566896003)
              ·
                refine ⟨49520452849938042850344005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33013635233292028566896003 49520452849938042850344005)
                ·
                  refine ⟨9285084909363383034439501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49520452849938042850344005 9285084909363383034439501)
                  ·
                    refine ⟨3481906841011268637914813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9285084909363383034439501 3481906841011268637914813)
                    ·
                      refine ⟨1305715065379225739218055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3481906841011268637914813 1305715065379225739218055)
                      ·
                        rfl

theorem cell23_2542871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 1, 4, 3, 3].length) (baseStart_2542871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542871 prefixEnd_2542871 := by exact prefixLift 2542871
  have htrace : WordTrace (prefixWord ++ tailWord_2542871) baseStart_2542871 baseEnd_2542871 := by
    simpa [prefixWord, tailWord_2542871, baseEnd_2542871] using wordTrace_append hprefix tailTrace_2542871
  have hstable : (prefixWord ++ tailWord_2542871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542871).length < 2 ^ (prefixWord ++ tailWord_2542871).sum := by decide
  have hdescent : baseEnd_2542871 < baseStart_2542871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542872 : List Nat := [2, 1, 2, 3, 1, 5, 1, 2, 2, 2, 2]
def baseStart_2542872 : Nat := 118140960795 + 2542872 * 2 ^ 59
def prefixEnd_2542872 : Nat := 4983230072969 + 3 ^ 40 * 2542872 * 2
def baseEnd_2542872 : Nat := 1305715578859880235305551

theorem tailTrace_2542872 : CollatzResearch.WordTrace tailWord_2542872 prefixEnd_2542872 1305715578859880235305551 := by
  unfold tailWord_2542872
  simp only [CollatzResearch.WordTrace]
  refine ⟨46373080621808253403639435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61830774162411004538185913 46373080621808253403639435)
  ·
    refine ⟨69559620932712380105459153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46373080621808253403639435 69559620932712380105459153)
    ·
      refine ⟨52169715699534285079094365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69559620932712380105459153 52169715699534285079094365)
      ·
        refine ⟨19563643387325356904660387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52169715699534285079094365 19563643387325356904660387)
        ·
          refine ⟨29345465080988035356990581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19563643387325356904660387 29345465080988035356990581)
          ·
            refine ⟨2751137351342628314717867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29345465080988035356990581 2751137351342628314717867)
            ·
              refine ⟨4126706027013942472076801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751137351342628314717867 4126706027013942472076801)
              ·
                refine ⟨3095029520260456854057601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4126706027013942472076801 3095029520260456854057601)
                ·
                  refine ⟨2321272140195342640543201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3095029520260456854057601 2321272140195342640543201)
                  ·
                    refine ⟨1740954105146506980407401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2321272140195342640543201 1740954105146506980407401)
                    ·
                      refine ⟨1305715578859880235305551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1740954105146506980407401 1305715578859880235305551)
                      ·
                        rfl

theorem cell23_2542872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2, 2, 2].length) (baseStart_2542872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542872 prefixEnd_2542872 := by exact prefixLift 2542872
  have htrace : WordTrace (prefixWord ++ tailWord_2542872) baseStart_2542872 baseEnd_2542872 := by
    simpa [prefixWord, tailWord_2542872, baseEnd_2542872] using wordTrace_append hprefix tailTrace_2542872
  have hstable : (prefixWord ++ tailWord_2542872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542872).length < 2 ^ (prefixWord ++ tailWord_2542872).sum := by decide
  have hdescent : baseEnd_2542872 < baseStart_2542872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542888 : List Nat := [2, 1, 5, 1, 2, 1, 2, 1, 2, 3, 3]
def baseStart_2542888 : Nat := 118140960795 + 2542888 * 2 ^ 59
def prefixEnd_2542888 : Nat := 4983230072969 + 3 ^ 40 * 2542888 * 2
def baseEnd_2542888 : Nat := 1305723794550352172705477

theorem tailTrace_2542888 : CollatzResearch.WordTrace tailWord_2542888 prefixEnd_2542888 1305723794550352172705477 := by
  unfold tailWord_2542888
  simp only [CollatzResearch.WordTrace]
  refine ⟨46373372405779270769930659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61831163207705694359907545 46373372405779270769930659)
  ·
    refine ⟨69560058608668906154895989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46373372405779270769930659 69560058608668906154895989)
    ·
      refine ⟨6521255494562709952021499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69560058608668906154895989 6521255494562709952021499)
      ·
        refine ⟨9781883241844064928032249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6521255494562709952021499 9781883241844064928032249)
        ·
          refine ⟨7336412431383048696024187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9781883241844064928032249 7336412431383048696024187)
          ·
            refine ⟨11004618647074573044036281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7336412431383048696024187 11004618647074573044036281)
            ·
              refine ⟨8253463985305929783027211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11004618647074573044036281 8253463985305929783027211)
              ·
                refine ⟨12380195977958894674540817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8253463985305929783027211 12380195977958894674540817)
                ·
                  refine ⟨9285146983469171005905613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12380195977958894674540817 9285146983469171005905613)
                  ·
                    refine ⟨3481930118800939127214605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9285146983469171005905613 3481930118800939127214605)
                    ·
                      refine ⟨1305723794550352172705477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3481930118800939127214605 1305723794550352172705477)
                      ·
                        rfl

theorem cell23_2542888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_2542888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542888 prefixEnd_2542888 := by exact prefixLift 2542888
  have htrace : WordTrace (prefixWord ++ tailWord_2542888) baseStart_2542888 baseEnd_2542888 := by
    simpa [prefixWord, tailWord_2542888, baseEnd_2542888] using wordTrace_append hprefix tailTrace_2542888
  have hstable : (prefixWord ++ tailWord_2542888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542888).length < 2 ^ (prefixWord ++ tailWord_2542888).sum := by decide
  have hdescent : baseEnd_2542888 < baseStart_2542888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542904 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 1, 10]
def baseStart_2542904 : Nat := 118140960795 + 2542904 * 2 ^ 59
def prefixEnd_2542904 : Nat := 4983230072969 + 3 ^ 40 * 2542904 * 2
def baseEnd_2542904 : Nat := 435244003413608036701801

theorem tailTrace_2542904 : CollatzResearch.WordTrace tailWord_2542904 prefixEnd_2542904 435244003413608036701801 := by
  unfold tailWord_2542904
  simp only [CollatzResearch.WordTrace]
  refine ⟨46373664189750288136221883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61831552253000384181629177 46373664189750288136221883)
  ·
    refine ⟨69560496284625432204332825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46373664189750288136221883 69560496284625432204332825)
    ·
      refine ⟨52170372213469074153249619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69560496284625432204332825 52170372213469074153249619)
      ·
        refine ⟨78255558320203611229874429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52170372213469074153249619 78255558320203611229874429)
        ·
          refine ⟨29345834370076354211202911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78255558320203611229874429 29345834370076354211202911)
          ·
            refine ⟨44018751555114531316804367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29345834370076354211202911 44018751555114531316804367)
            ·
              refine ⟨66028127332671796975206551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44018751555114531316804367 66028127332671796975206551)
              ·
                refine ⟨99042190999007695462809827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66028127332671796975206551 99042190999007695462809827)
                ·
                  refine ⟨148563286498511543194214741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99042190999007695462809827 148563286498511543194214741)
                  ·
                    refine ⟨435244003413608036701801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 148563286498511543194214741 435244003413608036701801)
                    ·
                      rfl

theorem cell23_2542904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 10].length) (baseStart_2542904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542904 prefixEnd_2542904 := by exact prefixLift 2542904
  have htrace : WordTrace (prefixWord ++ tailWord_2542904) baseStart_2542904 baseEnd_2542904 := by
    simpa [prefixWord, tailWord_2542904, baseEnd_2542904] using wordTrace_append hprefix tailTrace_2542904
  have hstable : (prefixWord ++ tailWord_2542904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542904).length < 2 ^ (prefixWord ++ tailWord_2542904).sum := by decide
  have hdescent : baseEnd_2542904 < baseStart_2542904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542911 : List Nat := [1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 4]
def baseStart_2542911 : Nat := 118140960795 + 2542911 * 2 ^ 59
def prefixEnd_2542911 : Nat := 4983230072969 + 3 ^ 40 * 2542911 * 2
def baseEnd_2542911 : Nat := 1305735604605405582717871

theorem tailTrace_2542911 : CollatzResearch.WordTrace tailWord_2542911 prefixEnd_2542911 1305735604605405582717871 := by
  unfold tailWord_2542911
  simp only [CollatzResearch.WordTrace]
  refine ⟨92747583690475216467948587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61831722460316810978632391 92747583690475216467948587)
  ·
    refine ⟨139121375535712824701922881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92747583690475216467948587 139121375535712824701922881)
    ·
      refine ⟨104341031651784618526442161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139121375535712824701922881 104341031651784618526442161)
      ·
        refine ⟨78255773738838463894831621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104341031651784618526442161 78255773738838463894831621)
        ·
          refine ⟨14672957576032211980280929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78255773738838463894831621 14672957576032211980280929)
          ·
            refine ⟨11004718182024158985210697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14672957576032211980280929 11004718182024158985210697)
            ·
              refine ⟨8253538636518119238908023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11004718182024158985210697 8253538636518119238908023)
              ·
                refine ⟨12380307954777178858362035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8253538636518119238908023 12380307954777178858362035)
                ·
                  refine ⟨18570461932165768287543053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12380307954777178858362035 18570461932165768287543053)
                  ·
                    refine ⟨6963923224562163107828645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18570461932165768287543053 6963923224562163107828645)
                    ·
                      refine ⟨1305735604605405582717871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6963923224562163107828645 1305735604605405582717871)
                      ·
                        rfl

theorem cell23_2542911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_2542911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542911 prefixEnd_2542911 := by exact prefixLift 2542911
  have htrace : WordTrace (prefixWord ++ tailWord_2542911) baseStart_2542911 baseEnd_2542911 := by
    simpa [prefixWord, tailWord_2542911, baseEnd_2542911] using wordTrace_append hprefix tailTrace_2542911
  have hstable : (prefixWord ++ tailWord_2542911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542911).length < 2 ^ (prefixWord ++ tailWord_2542911).sum := by decide
  have hdescent : baseEnd_2542911 < baseStart_2542911 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542921 : List Nat := [1, 2, 1, 1, 2, 3, 2, 2, 5, 4]
def baseStart_2542921 : Nat := 118140960795 + 2542921 * 2 ^ 59
def prefixEnd_2542921 : Nat := 4983230072969 + 3 ^ 40 * 2542921 * 2
def baseEnd_2542921 : Nat := 435246913137316847864275

theorem tailTrace_2542921 : CollatzResearch.WordTrace tailWord_2542921 prefixEnd_2542921 435246913137316847864275 := by
  unfold tailWord_2542921
  simp only [CollatzResearch.WordTrace]
  refine ⟨92747948420438988175812617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61831965613625992117208411 92747948420438988175812617)
  ·
    refine ⟨69560961315329241131859463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92747948420438988175812617 69560961315329241131859463)
    ·
      refine ⟨104341441972993861697789195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69560961315329241131859463 104341441972993861697789195)
      ·
        refine ⟨156512162959490792546683793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104341441972993861697789195 156512162959490792546683793)
        ·
          refine ⟨117384122219618094410012845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156512162959490792546683793 117384122219618094410012845)
          ·
            refine ⟨44019045832356785403754817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117384122219618094410012845 44019045832356785403754817)
            ·
              refine ⟨33014284374267589052816113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44019045832356785403754817 33014284374267589052816113)
              ·
                refine ⟨24760713280700691789612085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33014284374267589052816113 24760713280700691789612085)
                ·
                  refine ⟨2321316870065689855276133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24760713280700691789612085 2321316870065689855276133)
                  ·
                    refine ⟨435246913137316847864275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2321316870065689855276133 435246913137316847864275)
                    ·
                      rfl

theorem cell23_2542921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 5, 4].length) (baseStart_2542921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542921 prefixEnd_2542921 := by exact prefixLift 2542921
  have htrace : WordTrace (prefixWord ++ tailWord_2542921) baseStart_2542921 baseEnd_2542921 := by
    simpa [prefixWord, tailWord_2542921, baseEnd_2542921] using wordTrace_append hprefix tailTrace_2542921
  have hstable : (prefixWord ++ tailWord_2542921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542921).length < 2 ^ (prefixWord ++ tailWord_2542921).sum := by decide
  have hdescent : baseEnd_2542921 < baseStart_2542921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542938 : List Nat := [3, 1, 1, 2, 1, 2, 5, 1, 3, 4]
def baseStart_2542938 : Nat := 118140960795 + 2542938 * 2 ^ 59
def prefixEnd_2542938 : Nat := 4983230072969 + 3 ^ 40 * 2542938 * 2
def baseEnd_2542938 : Nat := 435249822861025659026749

theorem tailTrace_2542938 : CollatzResearch.WordTrace tailWord_2542938 prefixEnd_2542938 435249822861025659026749 := by
  unfold tailWord_2542938
  simp only [CollatzResearch.WordTrace]
  refine ⟨23187142115344350019795367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61832378974251600052787645 23187142115344350019795367)
  ·
    refine ⟨34780713173016525029693051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23187142115344350019795367 34780713173016525029693051)
    ·
      refine ⟨52171069759524787544539577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34780713173016525029693051 52171069759524787544539577)
      ·
        refine ⟨39128302319643590658404683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52171069759524787544539577 39128302319643590658404683)
        ·
          refine ⟨58692453479465385987607025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39128302319643590658404683 58692453479465385987607025)
          ·
            refine ⟨44019340109599039490705269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58692453479465385987607025 44019340109599039490705269)
            ·
              refine ⟨4126813135274909952253619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44019340109599039490705269 4126813135274909952253619)
              ·
                refine ⟨6190219702912364928380429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4126813135274909952253619 6190219702912364928380429)
                ·
                  refine ⟨2321332388592136848142661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6190219702912364928380429 2321332388592136848142661)
                  ·
                    refine ⟨435249822861025659026749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2321332388592136848142661 435249822861025659026749)
                    ·
                      rfl

theorem cell23_2542938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 1, 3, 4].length) (baseStart_2542938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542938 prefixEnd_2542938 := by exact prefixLift 2542938
  have htrace : WordTrace (prefixWord ++ tailWord_2542938) baseStart_2542938 baseEnd_2542938 := by
    simpa [prefixWord, tailWord_2542938, baseEnd_2542938] using wordTrace_append hprefix tailTrace_2542938
  have hstable : (prefixWord ++ tailWord_2542938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542938).length < 2 ^ (prefixWord ++ tailWord_2542938).sum := by decide
  have hdescent : baseEnd_2542938 < baseStart_2542938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2542961 : List Nat := [1, 2, 2, 2, 1, 2, 2, 1, 2, 5, 3]
def baseStart_2542961 : Nat := 118140960795 + 2542961 * 2 ^ 59
def prefixEnd_2542961 : Nat := 4983230072969 + 3 ^ 40 * 2542961 * 2
def baseEnd_2542961 : Nat := 1305761278638130387092641

theorem tailTrace_2542961 : CollatzResearch.WordTrace tailWord_2542961 prefixEnd_2542961 1305761278638130387092641 := by
  unfold tailWord_2542961
  simp only [CollatzResearch.WordTrace]
  refine ⟨92749407340294075007268737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61832938226862716671512491 92749407340294075007268737)
  ·
    refine ⟨69562055505220556255451553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92749407340294075007268737 69562055505220556255451553)
    ·
      refine ⟨52171541628915417191588665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69562055505220556255451553 52171541628915417191588665)
      ·
        refine ⟨39128656221686562893691499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52171541628915417191588665 39128656221686562893691499)
        ·
          refine ⟨58692984332529844340537249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39128656221686562893691499 58692984332529844340537249)
          ·
            refine ⟨44019738249397383255402937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58692984332529844340537249 44019738249397383255402937)
            ·
              refine ⟨33014803687048037441552203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44019738249397383255402937 33014803687048037441552203)
              ·
                refine ⟨49522205530572056162328305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33014803687048037441552203 49522205530572056162328305)
                ·
                  refine ⟨37141654147929042121746229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49522205530572056162328305 37141654147929042121746229)
                  ·
                    refine ⟨3482030076368347698913709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37141654147929042121746229 3482030076368347698913709)
                    ·
                      refine ⟨1305761278638130387092641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3482030076368347698913709 1305761278638130387092641)
                      ·
                        rfl

theorem cell23_2542961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_2542961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2542961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2542961 prefixEnd_2542961 := by exact prefixLift 2542961
  have htrace : WordTrace (prefixWord ++ tailWord_2542961) baseStart_2542961 baseEnd_2542961 := by
    simpa [prefixWord, tailWord_2542961, baseEnd_2542961] using wordTrace_append hprefix tailTrace_2542961
  have hstable : (prefixWord ++ tailWord_2542961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2542961).length < 2 ^ (prefixWord ++ tailWord_2542961).sum := by decide
  have hdescent : baseEnd_2542961 < baseStart_2542961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2542961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543029 : List Nat := [1, 3, 3, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_2543029 : Nat := 118140960795 + 2543029 * 2 ^ 59
def prefixEnd_2543029 : Nat := 4983230072969 + 3 ^ 40 * 2543029 * 2
def baseEnd_2543029 : Nat := 1305796195322636121042329

theorem tailTrace_2543029 : CollatzResearch.WordTrace tailWord_2543029 prefixEnd_2543029 1305796195322636121042329 := by
  unfold tailWord_2543029
  simp only [CollatzResearch.WordTrace]
  refine ⟨92751887504047722620744141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61834591669365148413829427 92751887504047722620744141)
  ·
    refine ⟨34781957814017895982779053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92751887504047722620744141 34781957814017895982779053)
    ·
      refine ⟨13043234180256710993542145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34781957814017895982779053 13043234180256710993542145)
      ·
        refine ⟨9782425635192533245156609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13043234180256710993542145 9782425635192533245156609)
        ·
          refine ⟨7336819226394399933867457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9782425635192533245156609 7336819226394399933867457)
          ·
            refine ⟨5502614419795799950400593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7336819226394399933867457 5502614419795799950400593)
            ·
              refine ⟨4126960814846849962800445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5502614419795799950400593 4126960814846849962800445)
              ·
                refine ⟨1547610305567568736050167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4126960814846849962800445 1547610305567568736050167)
                ·
                  refine ⟨2321415458351353104075251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547610305567568736050167 2321415458351353104075251)
                  ·
                    refine ⟨3482123187527029656112877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2321415458351353104075251 3482123187527029656112877)
                    ·
                      refine ⟨1305796195322636121042329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3482123187527029656112877 1305796195322636121042329)
                      ·
                        rfl

theorem cell23_2543029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_2543029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543029 prefixEnd_2543029 := by exact prefixLift 2543029
  have htrace : WordTrace (prefixWord ++ tailWord_2543029) baseStart_2543029 baseEnd_2543029 := by
    simpa [prefixWord, tailWord_2543029, baseEnd_2543029] using wordTrace_append hprefix tailTrace_2543029
  have hstable : (prefixWord ++ tailWord_2543029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543029).length < 2 ^ (prefixWord ++ tailWord_2543029).sum := by decide
  have hdescent : baseEnd_2543029 < baseStart_2543029 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543038 : List Nat := [4, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_2543038 : Nat := 118140960795 + 2543038 * 2 ^ 59
def prefixEnd_2543038 : Nat := 4983230072969 + 3 ^ 40 * 2543038 * 2
def baseEnd_2543038 : Nat := 1305800816648526585829787

theorem tailTrace_2543038 : CollatzResearch.WordTrace tailWord_2543038 prefixEnd_2543038 1305800816648526585829787 := by
  unfold tailWord_2543038
  simp only [CollatzResearch.WordTrace]
  refine ⟨11594026970126889644727721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61834810507343411438547845 11594026970126889644727721)
  ·
    refine ⟨8695520227595167233545791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11594026970126889644727721 8695520227595167233545791)
    ·
      refine ⟨13043280341392750850318687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8695520227595167233545791 13043280341392750850318687)
      ·
        refine ⟨19564920512089126275478031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13043280341392750850318687 19564920512089126275478031)
        ·
          refine ⟨29347380768133689413217047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19564920512089126275478031 29347380768133689413217047)
          ·
            refine ⟨44021071152200534119825571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29347380768133689413217047 44021071152200534119825571)
            ·
              refine ⟨66031606728300801179738357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44021071152200534119825571 66031606728300801179738357)
              ·
                refine ⟨6190463130778200110600471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66031606728300801179738357 6190463130778200110600471)
                ·
                  refine ⟨9285694696167300165900707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6190463130778200110600471 9285694696167300165900707)
                  ·
                    refine ⟨13928542044250950248851061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9285694696167300165900707 13928542044250950248851061)
                    ·
                      refine ⟨1305800816648526585829787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13928542044250950248851061 1305800816648526585829787)
                      ·
                        rfl

theorem cell23_2543038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_2543038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543038 prefixEnd_2543038 := by exact prefixLift 2543038
  have htrace : WordTrace (prefixWord ++ tailWord_2543038) baseStart_2543038 baseEnd_2543038 := by
    simpa [prefixWord, tailWord_2543038, baseEnd_2543038] using wordTrace_append hprefix tailTrace_2543038
  have hstable : (prefixWord ++ tailWord_2543038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543038).length < 2 ^ (prefixWord ++ tailWord_2543038).sum := by decide
  have hdescent : baseEnd_2543038 < baseStart_2543038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543052 : List Nat := [2, 2, 1, 4, 2, 1, 1, 3, 3, 2, 2]
def baseStart_2543052 : Nat := 118140960795 + 2543052 * 2 ^ 59
def prefixEnd_2543052 : Nat := 4983230072969 + 3 ^ 40 * 2543052 * 2
def baseEnd_2543052 : Nat := 1305808005377689531054723

theorem tailTrace_2543052 : CollatzResearch.WordTrace tailWord_2543052 prefixEnd_2543052 1305808005377689531054723 := by
  unfold tailWord_2543052
  simp only [CollatzResearch.WordTrace]
  refine ⟨46376363191482198774415705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61835150921976265032554273 46376363191482198774415705)
  ·
    refine ⟨34782272393611649080811779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46376363191482198774415705 34782272393611649080811779)
    ·
      refine ⟨52173408590417473621217669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34782272393611649080811779 52173408590417473621217669)
      ·
        refine ⟨9782514110703276303978313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52173408590417473621217669 9782514110703276303978313)
        ·
          refine ⟨7336885583027457227983735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9782514110703276303978313 7336885583027457227983735)
          ·
            refine ⟨11005328374541185841975603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7336885583027457227983735 11005328374541185841975603)
            ·
              refine ⟨16507992561811778762963405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11005328374541185841975603 16507992561811778762963405)
              ·
                refine ⟨6190497210679417036111277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16507992561811778762963405 6190497210679417036111277)
                ·
                  refine ⟨2321436454004781388541729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6190497210679417036111277 2321436454004781388541729)
                  ·
                    refine ⟨1741077340503586041406297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2321436454004781388541729 1741077340503586041406297)
                    ·
                      refine ⟨1305808005377689531054723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1741077340503586041406297 1305808005377689531054723)
                      ·
                        rfl

theorem cell23_2543052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_2543052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543052 prefixEnd_2543052 := by exact prefixLift 2543052
  have htrace : WordTrace (prefixWord ++ tailWord_2543052) baseStart_2543052 baseEnd_2543052 := by
    simpa [prefixWord, tailWord_2543052, baseEnd_2543052] using wordTrace_append hprefix tailTrace_2543052
  have hstable : (prefixWord ++ tailWord_2543052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543052).length < 2 ^ (prefixWord ++ tailWord_2543052).sum := by decide
  have hdescent : baseEnd_2543052 < baseStart_2543052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543062 : List Nat := [5, 2, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_2543062 : Nat := 118140960795 + 2543062 * 2 ^ 59
def prefixEnd_2543062 : Nat := 4983230072969 + 3 ^ 40 * 2543062 * 2
def baseEnd_2543062 : Nat := 435271046728078163976559

theorem tailTrace_2543062 : CollatzResearch.WordTrace tailWord_2543062 prefixEnd_2543062 435271046728078163976559 := by
  unfold tailWord_2543062
  simp only [CollatzResearch.WordTrace]
  refine ⟨5797068194558010578543465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61835394075285446171130293 5797068194558010578543465)
  ·
    refine ⟨4347801145918507933907599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5797068194558010578543465 4347801145918507933907599)
    ·
      refine ⟨6521701718877761900861399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4347801145918507933907599 6521701718877761900861399)
      ·
        refine ⟨9782552578316642851292099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6521701718877761900861399 9782552578316642851292099)
        ·
          refine ⟨14673828867474964276938149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9782552578316642851292099 14673828867474964276938149)
          ·
            refine ⟨2751342912651555801925903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14673828867474964276938149 2751342912651555801925903)
            ·
              refine ⟨4127014368977333702888855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751342912651555801925903 4127014368977333702888855)
              ·
                refine ⟨6190521553466000554333283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4127014368977333702888855 6190521553466000554333283)
                ·
                  refine ⟨9285782330199000831499925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6190521553466000554333283 9285782330199000831499925)
                  ·
                    refine ⟨435271046728078163976559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9285782330199000831499925 435271046728078163976559)
                    ·
                      rfl

theorem cell23_2543062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_2543062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543062 prefixEnd_2543062 := by exact prefixLift 2543062
  have htrace : WordTrace (prefixWord ++ tailWord_2543062) baseStart_2543062 baseEnd_2543062 := by
    simpa [prefixWord, tailWord_2543062, baseEnd_2543062] using wordTrace_append hprefix tailTrace_2543062
  have hstable : (prefixWord ++ tailWord_2543062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543062).length < 2 ^ (prefixWord ++ tailWord_2543062).sum := by decide
  have hdescent : baseEnd_2543062 < baseStart_2543062 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543065 : List Nat := [1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 4]
def baseStart_2543065 : Nat := 118140960795 + 2543065 * 2 ^ 59
def prefixEnd_2543065 : Nat := 4983230072969 + 3 ^ 40 * 2543065 * 2
def baseEnd_2543065 : Nat := 1305814680626197980192163

theorem tailTrace_2543065 : CollatzResearch.WordTrace tailWord_2543065 prefixEnd_2543065 1305814680626197980192163 := by
  unfold tailWord_2543065
  simp only [CollatzResearch.WordTrace]
  refine ⟨92753200531917300769054649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61835467021278200512703099 92753200531917300769054649)
  ·
    refine ⟨69564900398937975576790987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92753200531917300769054649 69564900398937975576790987)
    ·
      refine ⟨104347350598406963365186481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69564900398937975576790987 104347350598406963365186481)
      ·
        refine ⟨78260512948805222523889861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104347350598406963365186481 78260512948805222523889861)
        ·
          refine ⟨14673846177900979223229349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78260512948805222523889861 14673846177900979223229349)
          ·
            refine ⟨2751346158356433604355503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14673846177900979223229349 2751346158356433604355503)
            ·
              refine ⟨4127019237534650406533255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751346158356433604355503 4127019237534650406533255)
              ·
                refine ⟨6190528856301975609799883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4127019237534650406533255 6190528856301975609799883)
                ·
                  refine ⟨9285793284452963414699825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6190528856301975609799883 9285793284452963414699825)
                  ·
                    refine ⟨6964344963339722561024869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9285793284452963414699825 6964344963339722561024869)
                    ·
                      refine ⟨1305814680626197980192163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6964344963339722561024869 1305814680626197980192163)
                      ·
                        rfl

theorem cell23_2543065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_2543065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543065 prefixEnd_2543065 := by exact prefixLift 2543065
  have htrace : WordTrace (prefixWord ++ tailWord_2543065) baseStart_2543065 baseEnd_2543065 := by
    simpa [prefixWord, tailWord_2543065, baseEnd_2543065] using wordTrace_append hprefix tailTrace_2543065
  have hstable : (prefixWord ++ tailWord_2543065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543065).length < 2 ^ (prefixWord ++ tailWord_2543065).sum := by decide
  have hdescent : baseEnd_2543065 < baseStart_2543065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543075 : List Nat := [1, 1, 1, 6, 2, 3, 2, 7]
def baseStart_2543075 : Nat := 118140960795 + 2543075 * 2 ^ 59
def prefixEnd_2543075 : Nat := 4983230072969 + 3 ^ 40 * 2543075 * 2
def baseEnd_2543075 : Nat := 48363696867879368187671

theorem tailTrace_2543075 : CollatzResearch.WordTrace tailWord_2543075 prefixEnd_2543075 48363696867879368187671 := by
  unfold tailWord_2543075
  simp only [CollatzResearch.WordTrace]
  refine ⟨92753565261881072476918679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61835710174587381651279119 92753565261881072476918679)
  ·
    refine ⟨139130347892821608715378019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92753565261881072476918679 139130347892821608715378019)
    ·
      refine ⟨208695521839232413073067029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139130347892821608715378019 208695521839232413073067029)
      ·
        refine ⟨9782602586214019362800017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 208695521839232413073067029 9782602586214019362800017)
        ·
          refine ⟨7336951939660514522100013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9782602586214019362800017 7336951939660514522100013)
          ·
            refine ⟨2751356977372692945787505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7336951939660514522100013 2751356977372692945787505)
            ·
              refine ⟨2063517733029519709340629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2751356977372692945787505 2063517733029519709340629)
              ·
                refine ⟨48363696867879368187671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2063517733029519709340629 48363696867879368187671)
                ·
                  rfl

theorem cell23_2543075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 7].length) (baseStart_2543075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543075 prefixEnd_2543075 := by exact prefixLift 2543075
  have htrace : WordTrace (prefixWord ++ tailWord_2543075) baseStart_2543075 baseEnd_2543075 := by
    simpa [prefixWord, tailWord_2543075, baseEnd_2543075] using wordTrace_append hprefix tailTrace_2543075
  have hstable : (prefixWord ++ tailWord_2543075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543075).length < 2 ^ (prefixWord ++ tailWord_2543075).sum := by decide
  have hdescent : baseEnd_2543075 < baseStart_2543075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543159 : List Nat := [1, 1, 3, 1, 2, 5, 2, 2, 2, 2, 2]
def baseStart_2543159 : Nat := 118140960795 + 2543159 * 2 ^ 59
def prefixEnd_2543159 : Nat := 4983230072969 + 3 ^ 40 * 2543159 * 2
def baseEnd_2543159 : Nat := 1305862947807720612416731

theorem tailTrace_2543159 : CollatzResearch.WordTrace tailWord_2543159 prefixEnd_2543159 1305862947807720612416731 := by
  unfold tailWord_2543159
  simp only [CollatzResearch.WordTrace]
  refine ⟨92756628993576754822976531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61837752662384503215317687 92756628993576754822976531)
  ·
    refine ⟨139134943490365132234464797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92756628993576754822976531 139134943490365132234464797)
    ·
      refine ⟨52175603808886924587924299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139134943490365132234464797 52175603808886924587924299)
      ·
        refine ⟨78263405713330386881886449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52175603808886924587924299 78263405713330386881886449)
        ·
          refine ⟨58697554284997790161414837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78263405713330386881886449 58697554284997790161414837)
          ·
            refine ⟨5502895714218542827632641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58697554284997790161414837 5502895714218542827632641)
            ·
              refine ⟨4127171785663907120724481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5502895714218542827632641 4127171785663907120724481)
              ·
                refine ⟨3095378839247930340543361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4127171785663907120724481 3095378839247930340543361)
                ·
                  refine ⟨2321534129435947755407521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3095378839247930340543361 2321534129435947755407521)
                  ·
                    refine ⟨1741150597076960816555641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2321534129435947755407521 1741150597076960816555641)
                    ·
                      refine ⟨1305862947807720612416731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1741150597076960816555641 1305862947807720612416731)
                      ·
                        rfl

theorem cell23_2543159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 2, 2, 2, 2, 2].length) (baseStart_2543159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543159 prefixEnd_2543159 := by exact prefixLift 2543159
  have htrace : WordTrace (prefixWord ++ tailWord_2543159) baseStart_2543159 baseEnd_2543159 := by
    simpa [prefixWord, tailWord_2543159, baseEnd_2543159] using wordTrace_append hprefix tailTrace_2543159
  have hstable : (prefixWord ++ tailWord_2543159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543159).length < 2 ^ (prefixWord ++ tailWord_2543159).sum := by decide
  have hdescent : baseEnd_2543159 < baseStart_2543159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543178 : List Nat := [3, 1, 2, 1, 1, 3, 2, 2, 1, 7]
def baseStart_2543178 : Nat := 118140960795 + 2543178 * 2 ^ 59
def prefixEnd_2543178 : Nat := 4983230072969 + 3 ^ 40 * 2543178 * 2
def baseEnd_2543178 : Nat := 435290901313385346026381

theorem tailTrace_2543178 : CollatzResearch.WordTrace tailWord_2543178 prefixEnd_2543178 435290901313385346026381 := by
  unfold tailWord_2543178
  simp only [CollatzResearch.WordTrace]
  refine ⟨23189330495126980266979547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61838214653671947378612125 23189330495126980266979547)
  ·
    refine ⟨34783995742690470400469321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23189330495126980266979547 34783995742690470400469321)
    ·
      refine ⟨26087996807017852800351991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34783995742690470400469321 26087996807017852800351991)
      ·
        refine ⟨39131995210526779200527987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26087996807017852800351991 39131995210526779200527987)
        ·
          refine ⟨58697992815790168800791981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39131995210526779200527987 58697992815790168800791981)
          ·
            refine ⟨22011747305921313300296993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58697992815790168800791981 22011747305921313300296993)
            ·
              refine ⟨16508810479440984975222745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22011747305921313300296993 16508810479440984975222745)
              ·
                refine ⟨12381607859580738731417059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16508810479440984975222745 12381607859580738731417059)
                ·
                  refine ⟨18572411789371108097125589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12381607859580738731417059 18572411789371108097125589)
                  ·
                    refine ⟨435290901313385346026381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18572411789371108097125589 435290901313385346026381)
                    ·
                      rfl

theorem cell23_2543178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_2543178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543178 prefixEnd_2543178 := by exact prefixLift 2543178
  have htrace : WordTrace (prefixWord ++ tailWord_2543178) baseStart_2543178 baseEnd_2543178 := by
    simpa [prefixWord, tailWord_2543178, baseEnd_2543178] using wordTrace_append hprefix tailTrace_2543178
  have hstable : (prefixWord ++ tailWord_2543178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543178).length < 2 ^ (prefixWord ++ tailWord_2543178).sum := by decide
  have hdescent : baseEnd_2543178 < baseStart_2543178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543185 : List Nat := [1, 2, 2, 1, 3, 2, 1, 2, 2, 5, 2]
def baseStart_2543185 : Nat := 118140960795 + 2543185 * 2 ^ 59
def prefixEnd_2543185 : Nat := 4983230072969 + 3 ^ 40 * 2543185 * 2
def baseEnd_2543185 : Nat := 1305876298304737510691611

theorem tailTrace_2543185 : CollatzResearch.WordTrace tailWord_2543185 prefixEnd_2543185 1305876298304737510691611 := by
  unfold tailWord_2543185
  simp only [CollatzResearch.WordTrace]
  refine ⟨92757577291482561263423009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61838384860988374175615339 92757577291482561263423009)
  ·
    refine ⟨69568182968611920947567257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92757577291482561263423009 69568182968611920947567257)
    ·
      refine ⟨52176137226458940710675443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69568182968611920947567257 52176137226458940710675443)
      ·
        refine ⟨78264205839688411066013165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52176137226458940710675443 78264205839688411066013165)
        ·
          refine ⟨29349077189883154149754937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78264205839688411066013165 29349077189883154149754937)
          ·
            refine ⟨22011807892412365612316203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29349077189883154149754937 22011807892412365612316203)
            ·
              refine ⟨33017711838618548418474305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22011807892412365612316203 33017711838618548418474305)
              ·
                refine ⟨24763283878963911313855729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33017711838618548418474305 24763283878963911313855729)
                ·
                  refine ⟨18572462909222933485391797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24763283878963911313855729 18572462909222933485391797)
                  ·
                    refine ⟨1741168397739650014255481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18572462909222933485391797 1741168397739650014255481)
                    ·
                      refine ⟨1305876298304737510691611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1741168397739650014255481 1305876298304737510691611)
                      ·
                        rfl

theorem cell23_2543185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 5, 2].length) (baseStart_2543185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543185 prefixEnd_2543185 := by exact prefixLift 2543185
  have htrace : WordTrace (prefixWord ++ tailWord_2543185) baseStart_2543185 baseEnd_2543185 := by
    simpa [prefixWord, tailWord_2543185, baseEnd_2543185] using wordTrace_append hprefix tailTrace_2543185
  have hstable : (prefixWord ++ tailWord_2543185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543185).length < 2 ^ (prefixWord ++ tailWord_2543185).sum := by decide
  have hdescent : baseEnd_2543185 < baseStart_2543185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543228 : List Nat := [2, 2, 2, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_2543228 : Nat := 118140960795 + 2543228 * 2 ^ 59
def prefixEnd_2543228 : Nat := 4983230072969 + 3 ^ 40 * 2543228 * 2
def baseEnd_2543228 : Nat := 1305898377972880842453913

theorem tailTrace_2543228 : CollatzResearch.WordTrace tailWord_2543228 prefixEnd_2543228 1305898377972880842453913 := by
  unfold tailWord_2543228
  simp only [CollatzResearch.WordTrace]
  refine ⟨46379572815163389803619169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61839430420217853071492225 46379572815163389803619169)
  ·
    refine ⟨34784679611372542352714377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46379572815163389803619169 34784679611372542352714377)
    ·
      refine ⟨26088509708529406764535783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34784679611372542352714377 26088509708529406764535783)
      ·
        refine ⟨39132764562794110146803675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26088509708529406764535783 39132764562794110146803675)
        ·
          refine ⟨58699146844191165220205513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39132764562794110146803675 58699146844191165220205513)
          ·
            refine ⟨44024360133143373915154135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58699146844191165220205513 44024360133143373915154135)
            ·
              refine ⟨66036540199715060872731203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44024360133143373915154135 66036540199715060872731203)
              ·
                refine ⟨99054810299572591309096805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66036540199715060872731203 99054810299572591309096805)
                ·
                  refine ⟨18572776931169860870455651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 99054810299572591309096805 18572776931169860870455651)
                  ·
                    refine ⟨27859165396754791305683477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18572776931169860870455651 27859165396754791305683477)
                    ·
                      refine ⟨1305898377972880842453913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27859165396754791305683477 1305898377972880842453913)
                      ·
                        rfl

theorem cell23_2543228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_2543228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543228 prefixEnd_2543228 := by exact prefixLift 2543228
  have htrace : WordTrace (prefixWord ++ tailWord_2543228) baseStart_2543228 baseEnd_2543228 := by
    simpa [prefixWord, tailWord_2543228, baseEnd_2543228] using wordTrace_append hprefix tailTrace_2543228
  have hstable : (prefixWord ++ tailWord_2543228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543228).length < 2 ^ (prefixWord ++ tailWord_2543228).sum := by decide
  have hdescent : baseEnd_2543228 < baseStart_2543228 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543242 : List Nat := [3, 1, 2, 3, 2, 1, 2, 2, 3, 4]
def baseStart_2543242 : Nat := 118140960795 + 2543242 * 2 ^ 59
def prefixEnd_2543242 : Nat := 4983230072969 + 3 ^ 40 * 2543242 * 2
def baseEnd_2543242 : Nat := 435301855567347929226283

theorem tailTrace_2543242 : CollatzResearch.WordTrace tailWord_2543242 prefixEnd_2543242 435301855567347929226283 := by
  unfold tailWord_2543242
  simp only [CollatzResearch.WordTrace]
  refine ⟨23189914063069014999561995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61839770834850706665498653 23189914063069014999561995)
  ·
    refine ⟨34784871094603522499342993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23189914063069014999561995 34784871094603522499342993)
    ·
      refine ⟨26088653320952641874507245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34784871094603522499342993 26088653320952641874507245)
      ·
        refine ⟨9783244995357240702940217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26088653320952641874507245 9783244995357240702940217)
        ·
          refine ⟨7337433746517930527205163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9783244995357240702940217 7337433746517930527205163)
          ·
            refine ⟨11006150619776895790807745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7337433746517930527205163 11006150619776895790807745)
            ·
              refine ⟨8254612964832671843105809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11006150619776895790807745 8254612964832671843105809)
              ·
                refine ⟨6190959723624503882329357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8254612964832671843105809 6190959723624503882329357)
                ·
                  refine ⟨2321609896359188955873509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6190959723624503882329357 2321609896359188955873509)
                  ·
                    refine ⟨435301855567347929226283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2321609896359188955873509 435301855567347929226283)
                    ·
                      rfl

theorem cell23_2543242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 3, 4].length) (baseStart_2543242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543242 prefixEnd_2543242 := by exact prefixLift 2543242
  have htrace : WordTrace (prefixWord ++ tailWord_2543242) baseStart_2543242 baseEnd_2543242 := by
    simpa [prefixWord, tailWord_2543242, baseEnd_2543242] using wordTrace_append hprefix tailTrace_2543242
  have hstable : (prefixWord ++ tailWord_2543242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543242).length < 2 ^ (prefixWord ++ tailWord_2543242).sum := by decide
  have hdescent : baseEnd_2543242 < baseStart_2543242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543275 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 1, 11, 2]
def baseStart_2543275 : Nat := 118140960795 + 2543275 * 2 ^ 59
def prefixEnd_2543275 : Nat := 4983230072969 + 3 ^ 40 * 2543275 * 2
def baseEnd_2543275 : Nat := 1305922511563642158566197

theorem tailTrace_2543275 : CollatzResearch.WordTrace tailWord_2543275 prefixEnd_2543275 1305922511563642158566197 := by
  unfold tailWord_2543275
  simp only [CollatzResearch.WordTrace]
  refine ⟨92760859861156506634199279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61840573240771004422799519 92760859861156506634199279)
  ·
    refine ⟨139141289791734759951298919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92760859861156506634199279 139141289791734759951298919)
    ·
      refine ⟨208711934687602139926948379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139141289791734759951298919 208711934687602139926948379)
      ·
        refine ⟨313067902031403209890422569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208711934687602139926948379 313067902031403209890422569)
        ·
          refine ⟨234800926523552407417816927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313067902031403209890422569 234800926523552407417816927)
          ·
            refine ⟨352201389785328611126725391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234800926523552407417816927 352201389785328611126725391)
            ·
              refine ⟨528302084677992916690088087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 352201389785328611126725391 528302084677992916690088087)
              ·
                refine ⟨792453127016989375035132131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 528302084677992916690088087 792453127016989375035132131)
                ·
                  refine ⟨1188679690525484062552698197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 792453127016989375035132131 1188679690525484062552698197)
                  ·
                    refine ⟨1741230015418189544754929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 1188679690525484062552698197 1741230015418189544754929)
                    ·
                      refine ⟨1305922511563642158566197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1741230015418189544754929 1305922511563642158566197)
                      ·
                        rfl

theorem cell23_2543275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 11, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 11, 2].length) (baseStart_2543275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543275 prefixEnd_2543275 := by exact prefixLift 2543275
  have htrace : WordTrace (prefixWord ++ tailWord_2543275) baseStart_2543275 baseEnd_2543275 := by
    simpa [prefixWord, tailWord_2543275, baseEnd_2543275] using wordTrace_append hprefix tailTrace_2543275
  have hstable : (prefixWord ++ tailWord_2543275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543275).length < 2 ^ (prefixWord ++ tailWord_2543275).sum := by decide
  have hdescent : baseEnd_2543275 < baseStart_2543275 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543342 : List Nat := [4, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_2543342 : Nat := 118140960795 + 2543342 * 2 ^ 59
def prefixEnd_2543342 : Nat := 4983230072969 + 3 ^ 40 * 2543342 * 2
def baseEnd_2543342 : Nat := 1305956914767493396428389

theorem tailTrace_2543342 : CollatzResearch.WordTrace tailWord_2543342 prefixEnd_2543342 1305956914767493396428389 := by
  unfold tailWord_2543342
  simp only [CollatzResearch.WordTrace]
  refine ⟨11595412943989222134611035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61842202367942518051258853 11595412943989222134611035)
  ·
    refine ⟨17393119415983833201916553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11595412943989222134611035 17393119415983833201916553)
    ·
      refine ⟨13044839561987874901437415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17393119415983833201916553 13044839561987874901437415)
      ·
        refine ⟨19567259342981812352156123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13044839561987874901437415 19567259342981812352156123)
        ·
          refine ⟨29350889014472718528234185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19567259342981812352156123 29350889014472718528234185)
          ·
            refine ⟨22013166760854538896175639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29350889014472718528234185 22013166760854538896175639)
            ·
              refine ⟨33019750141281808344263459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22013166760854538896175639 33019750141281808344263459)
              ·
                refine ⟨49529625211922712516395189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33019750141281808344263459 49529625211922712516395189)
                ·
                  refine ⟨4643402363617754298412049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49529625211922712516395189 4643402363617754298412049)
                  ·
                    refine ⟨3482551772713315723809037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4643402363617754298412049 3482551772713315723809037)
                    ·
                      refine ⟨1305956914767493396428389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3482551772713315723809037 1305956914767493396428389)
                      ·
                        rfl

theorem cell23_2543342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_2543342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543342 prefixEnd_2543342 := by exact prefixLift 2543342
  have htrace : WordTrace (prefixWord ++ tailWord_2543342) baseStart_2543342 baseEnd_2543342 := by
    simpa [prefixWord, tailWord_2543342, baseEnd_2543342] using wordTrace_append hprefix tailTrace_2543342
  have hstable : (prefixWord ++ tailWord_2543342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543342).length < 2 ^ (prefixWord ++ tailWord_2543342).sum := by decide
  have hdescent : baseEnd_2543342 < baseStart_2543342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543345 : List Nat := [1, 2, 2, 2, 2, 3, 3, 8]
def baseStart_2543345 : Nat := 118140960795 + 2543345 * 2 ^ 59
def prefixEnd_2543345 : Nat := 4983230072969 + 3 ^ 40 * 2543345 * 2
def baseEnd_2543345 : Nat := 48368831674424329062625

theorem tailTrace_2543345 : CollatzResearch.WordTrace tailWord_2543345 prefixEnd_2543345 48368831674424329062625 := by
  unfold tailWord_2543345
  simp only [CollatzResearch.WordTrace]
  refine ⟨92763412970902908589247489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61842275313935272392831659 92763412970902908589247489)
  ·
    refine ⟨69572559728177181441935617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92763412970902908589247489 69572559728177181441935617)
    ·
      refine ⟨52179419796132886081451713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69572559728177181441935617 52179419796132886081451713)
      ·
        refine ⟨39134564847099664561088785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52179419796132886081451713 39134564847099664561088785)
        ·
          refine ⟨29350923635324748420816589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39134564847099664561088785 29350923635324748420816589)
          ·
            refine ⟨11006596363246780657806221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29350923635324748420816589 11006596363246780657806221)
            ·
              refine ⟨4127473636217542746677333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11006596363246780657806221 4127473636217542746677333)
              ·
                refine ⟨48368831674424329062625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4127473636217542746677333 48368831674424329062625)
                ·
                  rfl

theorem cell23_2543345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 8].length) (baseStart_2543345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543345 prefixEnd_2543345 := by exact prefixLift 2543345
  have htrace : WordTrace (prefixWord ++ tailWord_2543345) baseStart_2543345 baseEnd_2543345 := by
    simpa [prefixWord, tailWord_2543345, baseEnd_2543345] using wordTrace_append hprefix tailTrace_2543345
  have hstable : (prefixWord ++ tailWord_2543345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543345).length < 2 ^ (prefixWord ++ tailWord_2543345).sum := by decide
  have hdescent : baseEnd_2543345 < baseStart_2543345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543372 : List Nat := [2, 2, 1, 2, 2, 1, 4, 2, 1, 3, 3]
def baseStart_2543372 : Nat := 118140960795 + 2543372 * 2 ^ 59
def prefixEnd_2543372 : Nat := 4983230072969 + 3 ^ 40 * 2543372 * 2
def baseEnd_2543372 : Nat := 1305972319187128279053251

theorem tailTrace_2543372 : CollatzResearch.WordTrace tailWord_2543372 prefixEnd_2543372 1305972319187128279053251 := by
  unfold tailWord_2543372
  simp only [CollatzResearch.WordTrace]
  refine ⟨46382198870902546100240185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61842931827870061466986913 46382198870902546100240185)
  ·
    refine ⟨34786649153176909575180139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46382198870902546100240185 34786649153176909575180139)
    ·
      refine ⟨52179973729765364362770209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34786649153176909575180139 52179973729765364362770209)
      ·
        refine ⟨39134980297324023272077657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52179973729765364362770209 39134980297324023272077657)
        ·
          refine ⟨29351235222993017454058243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39134980297324023272077657 29351235222993017454058243)
          ·
            refine ⟨44026852834489526181087365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29351235222993017454058243 44026852834489526181087365)
            ·
              refine ⟨8255034906466786158953881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44026852834489526181087365 8255034906466786158953881)
              ·
                refine ⟨6191276179850089619215411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8255034906466786158953881 6191276179850089619215411)
                ·
                  refine ⟨9286914269775134428823117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6191276179850089619215411 9286914269775134428823117)
                  ·
                    refine ⟨3482592851165675410808669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9286914269775134428823117 3482592851165675410808669)
                    ·
                      refine ⟨1305972319187128279053251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3482592851165675410808669 1305972319187128279053251)
                      ·
                        rfl

theorem cell23_2543372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_2543372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543372 prefixEnd_2543372 := by exact prefixLift 2543372
  have htrace : WordTrace (prefixWord ++ tailWord_2543372) baseStart_2543372 baseEnd_2543372 := by
    simpa [prefixWord, tailWord_2543372, baseEnd_2543372] using wordTrace_append hprefix tailTrace_2543372
  have hstable : (prefixWord ++ tailWord_2543372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543372).length < 2 ^ (prefixWord ++ tailWord_2543372).sum := by decide
  have hdescent : baseEnd_2543372 < baseStart_2543372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543395 : List Nat := [1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 4]
def baseStart_2543395 : Nat := 118140960795 + 2543395 * 2 ^ 59
def prefixEnd_2543395 : Nat := 4983230072969 + 3 ^ 40 * 2543395 * 2
def baseEnd_2543395 : Nat := 1305984129242181689065645

theorem tailTrace_2543395 : CollatzResearch.WordTrace tailWord_2543395 prefixEnd_2543395 1305984129242181689065645 := by
  unfold tailWord_2543395
  simp only [CollatzResearch.WordTrace]
  refine ⟨92765236620721767128567639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61843491080481178085711759 92765236620721767128567639)
  ·
    refine ⟨139147854931082650692851459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92765236620721767128567639 139147854931082650692851459)
    ·
      refine ⟨208721782396623976039277189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139147854931082650692851459 208721782396623976039277189)
      ·
        refine ⟨39135334199366995507364473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208721782396623976039277189 39135334199366995507364473)
        ·
          refine ⟨29351500649525246630523355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39135334199366995507364473 29351500649525246630523355)
          ·
            refine ⟨44027250974287869945785033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29351500649525246630523355 44027250974287869945785033)
            ·
              refine ⟨33020438230715902459338775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44027250974287869945785033 33020438230715902459338775)
              ·
                refine ⟨49530657346073853689008163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33020438230715902459338775 49530657346073853689008163)
                ·
                  refine ⟨74295986019110780533512245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49530657346073853689008163 74295986019110780533512245)
                  ·
                    refine ⟨6965248689291635675016773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 74295986019110780533512245 6965248689291635675016773)
                    ·
                      refine ⟨1305984129242181689065645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6965248689291635675016773 1305984129242181689065645)
                      ·
                        rfl

theorem cell23_2543395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_2543395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543395 prefixEnd_2543395 := by exact prefixLift 2543395
  have htrace : WordTrace (prefixWord ++ tailWord_2543395) baseStart_2543395 baseEnd_2543395 := by
    simpa [prefixWord, tailWord_2543395, baseEnd_2543395] using wordTrace_append hprefix tailTrace_2543395
  have hstable : (prefixWord ++ tailWord_2543395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543395).length < 2 ^ (prefixWord ++ tailWord_2543395).sum := by decide
  have hdescent : baseEnd_2543395 < baseStart_2543395 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543416 : List Nat := [2, 1, 2, 1, 3, 4, 2, 2, 1, 3, 2]
def baseStart_2543416 : Nat := 118140960795 + 2543416 * 2 ^ 59
def prefixEnd_2543416 : Nat := 4983230072969 + 3 ^ 40 * 2543416 * 2
def baseEnd_2543416 : Nat := 1305994912335926106903049

theorem tailTrace_2543416 : CollatzResearch.WordTrace tailWord_2543416 prefixEnd_2543416 1305994912335926106903049 := by
  unfold tailWord_2543416
  simp only [CollatzResearch.WordTrace]
  refine ⟨46383001276822843857541051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61844001702430458476721401 46383001276822843857541051)
  ·
    refine ⟨69574501915234265786311577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46383001276822843857541051 69574501915234265786311577)
    ·
      refine ⟨52180876436425699339733683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69574501915234265786311577 52180876436425699339733683)
      ·
        refine ⟨78271314654638549009600525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52180876436425699339733683 78271314654638549009600525)
        ·
          refine ⟨29351742995489455878600197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78271314654638549009600525 29351742995489455878600197)
          ·
            refine ⟨5503451811654272977237537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29351742995489455878600197 5503451811654272977237537)
            ·
              refine ⟨4127588858740704732928153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5503451811654272977237537 4127588858740704732928153)
              ·
                refine ⟨3095691644055528549696115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4127588858740704732928153 3095691644055528549696115)
                ·
                  refine ⟨4643537466083292824544173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3095691644055528549696115 4643537466083292824544173)
                  ·
                    refine ⟨1741326549781234809204065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4643537466083292824544173 1741326549781234809204065)
                    ·
                      refine ⟨1305994912335926106903049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1741326549781234809204065 1305994912335926106903049)
                      ·
                        rfl

theorem cell23_2543416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 4, 2, 2, 1, 3, 2].length) (baseStart_2543416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543416 prefixEnd_2543416 := by exact prefixLift 2543416
  have htrace : WordTrace (prefixWord ++ tailWord_2543416) baseStart_2543416 baseEnd_2543416 := by
    simpa [prefixWord, tailWord_2543416, baseEnd_2543416] using wordTrace_append hprefix tailTrace_2543416
  have hstable : (prefixWord ++ tailWord_2543416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543416).length < 2 ^ (prefixWord ++ tailWord_2543416).sum := by decide
  have hdescent : baseEnd_2543416 < baseStart_2543416 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543429 : List Nat := [1, 3, 1, 1, 1, 2, 3, 1, 6, 2, 2]
def baseStart_2543429 : Nat := 118140960795 + 2543429 * 2 ^ 59
def prefixEnd_2543429 : Nat := 4983230072969 + 3 ^ 40 * 2543429 * 2
def baseEnd_2543429 : Nat := 1306001587584434556040489

theorem tailTrace_2543429 : CollatzResearch.WordTrace tailWord_2543429 prefixEnd_2543429 1306001587584434556040489 := by
  unfold tailWord_2543429
  simp only [CollatzResearch.WordTrace]
  refine ⟨92766476702598590935305341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61844317801732393956870227 92766476702598590935305341)
  ·
    refine ⟨34787428763474471600739503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92766476702598590935305341 34787428763474471600739503)
    ·
      refine ⟨52181143145211707401109255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34787428763474471600739503 52181143145211707401109255)
      ·
        refine ⟨78271714717817561101663883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52181143145211707401109255 78271714717817561101663883)
        ·
          refine ⟨117407572076726341652495825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78271714717817561101663883 117407572076726341652495825)
          ·
            refine ⟨88055679057544756239371869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117407572076726341652495825 88055679057544756239371869)
            ·
              refine ⟨33020879646579283589764451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88055679057544756239371869 33020879646579283589764451)
              ·
                refine ⟨49531319469868925384646677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33020879646579283589764451 49531319469868925384646677)
                ·
                  refine ⟨2321780600150105877405313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49531319469868925384646677 2321780600150105877405313)
                  ·
                    refine ⟨1741335450112579408053985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2321780600150105877405313 1741335450112579408053985)
                    ·
                      refine ⟨1306001587584434556040489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1741335450112579408053985 1306001587584434556040489)
                      ·
                        rfl

theorem cell23_2543429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 1, 6, 2, 2].length) (baseStart_2543429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543429 prefixEnd_2543429 := by exact prefixLift 2543429
  have htrace : WordTrace (prefixWord ++ tailWord_2543429) baseStart_2543429 baseEnd_2543429 := by
    simpa [prefixWord, tailWord_2543429, baseEnd_2543429] using wordTrace_append hprefix tailTrace_2543429
  have hstable : (prefixWord ++ tailWord_2543429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543429).length < 2 ^ (prefixWord ++ tailWord_2543429).sum := by decide
  have hdescent : baseEnd_2543429 < baseStart_2543429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543432 : List Nat := [2, 1, 3, 1, 1, 5, 1, 1, 2, 1, 5]
def baseStart_2543432 : Nat := 118140960795 + 2543432 * 2 ^ 59
def prefixEnd_2543432 : Nat := 4983230072969 + 3 ^ 40 * 2543432 * 2
def baseEnd_2543432 : Nat := 1306003128026398044302975

theorem tailTrace_2543432 : CollatzResearch.WordTrace tailWord_2543432 prefixEnd_2543432 1306003128026398044302975 := by
  unfold tailWord_2543432
  simp only [CollatzResearch.WordTrace]
  refine ⟨46383293060793861223832275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61844390747725148298443033 46383293060793861223832275)
  ·
    refine ⟨69574939591190791835748413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46383293060793861223832275 69574939591190791835748413)
    ·
      refine ⟨26090602346696546938405655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69574939591190791835748413 26090602346696546938405655)
      ·
        refine ⟨39135903520044820407608483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26090602346696546938405655 39135903520044820407608483)
        ·
          refine ⟨58703855280067230611412725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39135903520044820407608483 58703855280067230611412725)
          ·
            refine ⟨5503486432506302869819943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58703855280067230611412725 5503486432506302869819943)
            ·
              refine ⟨8255229648759454304729915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5503486432506302869819943 8255229648759454304729915)
              ·
                refine ⟨12382844473139181457094873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8255229648759454304729915 12382844473139181457094873)
                ·
                  refine ⟨9287133354854386092821155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12382844473139181457094873 9287133354854386092821155)
                  ·
                    refine ⟨13930700032281579139231733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9287133354854386092821155 13930700032281579139231733)
                    ·
                      refine ⟨1306003128026398044302975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13930700032281579139231733 1306003128026398044302975)
                      ·
                        rfl

theorem cell23_2543432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_2543432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543432 prefixEnd_2543432 := by exact prefixLift 2543432
  have htrace : WordTrace (prefixWord ++ tailWord_2543432) baseStart_2543432 baseEnd_2543432 := by
    simpa [prefixWord, tailWord_2543432, baseEnd_2543432] using wordTrace_append hprefix tailTrace_2543432
  have hstable : (prefixWord ++ tailWord_2543432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543432).length < 2 ^ (prefixWord ++ tailWord_2543432).sum := by decide
  have hdescent : baseEnd_2543432 < baseStart_2543432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543465 : List Nat := [1, 2, 1, 1, 1, 3, 1, 3, 3, 7]
def baseStart_2543465 : Nat := 118140960795 + 2543465 * 2 ^ 59
def prefixEnd_2543465 : Nat := 4983230072969 + 3 ^ 40 * 2543465 * 2
def baseEnd_2543465 : Nat := 435340024295998805063441

theorem tailTrace_2543465 : CollatzResearch.WordTrace tailWord_2543465 prefixEnd_2543465 435340024295998805063441 := by
  unfold tailWord_2543465
  simp only [CollatzResearch.WordTrace]
  refine ⟨92767789730468169083615849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61845193153645446055743899 92767789730468169083615849)
  ·
    refine ⟨69575842297851126812711887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92767789730468169083615849 69575842297851126812711887)
    ·
      refine ⟨104363763446776690219067831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69575842297851126812711887 104363763446776690219067831)
      ·
        refine ⟨156545645170165035328601747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104363763446776690219067831 156545645170165035328601747)
        ·
          refine ⟨234818467755247552992902621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156545645170165035328601747 234818467755247552992902621)
          ·
            refine ⟨88056925408217832372338483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234818467755247552992902621 88056925408217832372338483)
            ·
              refine ⟨132085388112326748558507725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88056925408217832372338483 132085388112326748558507725)
              ·
                refine ⟨49532020542122530709440397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132085388112326748558507725 49532020542122530709440397)
                ·
                  refine ⟨18574507703295949016040149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49532020542122530709440397 18574507703295949016040149)
                  ·
                    refine ⟨435340024295998805063441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 18574507703295949016040149 435340024295998805063441)
                    ·
                      rfl

theorem cell23_2543465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 7].length) (baseStart_2543465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543465 prefixEnd_2543465 := by exact prefixLift 2543465
  have htrace : WordTrace (prefixWord ++ tailWord_2543465) baseStart_2543465 baseEnd_2543465 := by
    simpa [prefixWord, tailWord_2543465, baseEnd_2543465] using wordTrace_append hprefix tailTrace_2543465
  have hstable : (prefixWord ++ tailWord_2543465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543465).length < 2 ^ (prefixWord ++ tailWord_2543465).sum := by decide
  have hdescent : baseEnd_2543465 < baseStart_2543465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543475 : List Nat := [1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 7]
def baseStart_2543475 : Nat := 118140960795 + 2543475 * 2 ^ 59
def prefixEnd_2543475 : Nat := 4983230072969 + 3 ^ 40 * 2543475 * 2
def baseEnd_2543475 : Nat := 1306025207694541376065277

theorem tailTrace_2543475 : CollatzResearch.WordTrace tailWord_2543475 prefixEnd_2543475 1306025207694541376065277 := by
  unfold tailWord_2543475
  simp only [CollatzResearch.WordTrace]
  refine ⟨92768154460431940791479879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61845436306954627194319919 92768154460431940791479879)
  ·
    refine ⟨139152231690647911187219819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92768154460431940791479879 139152231690647911187219819)
    ·
      refine ⟨208728347535971866780829729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139152231690647911187219819 208728347535971866780829729)
      ·
        refine ⟨156546260651978900085622297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 208728347535971866780829729 156546260651978900085622297)
        ·
          refine ⟨117409695488984175064216723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156546260651978900085622297 117409695488984175064216723)
          ·
            refine ⟨176114543233476262596325085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117409695488984175064216723 176114543233476262596325085)
            ·
              refine ⟨66042953712553598473621907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176114543233476262596325085 66042953712553598473621907)
              ·
                refine ⟨99064430568830397710432861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66042953712553598473621907 99064430568830397710432861)
                ·
                  refine ⟨37149161463311399141412323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99064430568830397710432861 37149161463311399141412323)
                  ·
                    refine ⟨55723742194967098712118485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37149161463311399141412323 55723742194967098712118485)
                    ·
                      refine ⟨1306025207694541376065277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55723742194967098712118485 1306025207694541376065277)
                      ·
                        rfl

theorem cell23_2543475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 7].length) (baseStart_2543475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543475 prefixEnd_2543475 := by exact prefixLift 2543475
  have htrace : WordTrace (prefixWord ++ tailWord_2543475) baseStart_2543475 baseEnd_2543475 := by
    simpa [prefixWord, tailWord_2543475, baseEnd_2543475] using wordTrace_append hprefix tailTrace_2543475
  have hstable : (prefixWord ++ tailWord_2543475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543475).length < 2 ^ (prefixWord ++ tailWord_2543475).sum := by decide
  have hdescent : baseEnd_2543475 < baseStart_2543475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543482 : List Nat := [3, 1, 1, 1, 1, 1, 5, 3, 2, 5]
def baseStart_2543482 : Nat := 118140960795 + 2543482 * 2 ^ 59
def prefixEnd_2543482 : Nat := 4983230072969 + 3 ^ 40 * 2543482 * 2
def baseEnd_2543482 : Nat := 435342934019707616225915

theorem tailTrace_2543482 : CollatzResearch.WordTrace tailWord_2543482 prefixEnd_2543482 435342934019707616225915 := by
  unfold tailWord_2543482
  simp only [CollatzResearch.WordTrace]
  refine ⟨23192102442851645246746175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61845606514271053991323133 23192102442851645246746175)
  ·
    refine ⟨34788153664277467870119263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23192102442851645246746175 34788153664277467870119263)
    ·
      refine ⟨52182230496416201805178895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34788153664277467870119263 52182230496416201805178895)
      ·
        refine ⟨78273345744624302707768343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52182230496416201805178895 78273345744624302707768343)
        ·
          refine ⟨117410018616936454061652515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78273345744624302707768343 117410018616936454061652515)
          ·
            refine ⟨176115027925404681092478773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117410018616936454061652515 176115027925404681092478773)
            ·
              refine ⟨16510783868006688852419885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 176115027925404681092478773 16510783868006688852419885)
              ·
                refine ⟨6191543950502508319657457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16510783868006688852419885 6191543950502508319657457)
                ·
                  refine ⟨4643657962876881239743093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6191543950502508319657457 4643657962876881239743093)
                  ·
                    refine ⟨435342934019707616225915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4643657962876881239743093 435342934019707616225915)
                    ·
                      rfl

theorem cell23_2543482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3, 2, 5].length) (baseStart_2543482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543482 prefixEnd_2543482 := by exact prefixLift 2543482
  have htrace : WordTrace (prefixWord ++ tailWord_2543482) baseStart_2543482 baseEnd_2543482 := by
    simpa [prefixWord, tailWord_2543482, baseEnd_2543482] using wordTrace_append hprefix tailTrace_2543482
  have hstable : (prefixWord ++ tailWord_2543482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543482).length < 2 ^ (prefixWord ++ tailWord_2543482).sum := by decide
  have hdescent : baseEnd_2543482 < baseStart_2543482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543492 : List Nat := [2, 3, 2, 1, 1, 1, 3, 2, 1, 2, 5]
def baseStart_2543492 : Nat := 118140960795 + 2543492 * 2 ^ 59
def prefixEnd_2543492 : Nat := 4983230072969 + 3 ^ 40 * 2543492 * 2
def baseEnd_2543492 : Nat := 1306033936865667809552699

theorem tailTrace_2543492 : CollatzResearch.WordTrace tailWord_2543492 prefixEnd_2543492 1306033936865667809552699 := by
  unfold tailWord_2543492
  simp only [CollatzResearch.WordTrace]
  refine ⟨46384387250685176347424365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61845849667580235129899153 46384387250685176347424365)
  ·
    refine ⟨17394145219006941130284137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46384387250685176347424365 17394145219006941130284137)
    ·
      refine ⟨13045608914255205847713103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17394145219006941130284137 13045608914255205847713103)
      ·
        refine ⟨19568413371382808771569655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13045608914255205847713103 19568413371382808771569655)
        ·
          refine ⟨29352620057074213157354483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19568413371382808771569655 29352620057074213157354483)
          ·
            refine ⟨44028930085611319736031725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29352620057074213157354483 44028930085611319736031725)
            ·
              refine ⟨16510848782104244901011897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44028930085611319736031725 16510848782104244901011897)
              ·
                refine ⟨12383136586578183675758923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16510848782104244901011897 12383136586578183675758923)
                ·
                  refine ⟨18574704879867275513638385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12383136586578183675758923 18574704879867275513638385)
                  ·
                    refine ⟨13931028659900456635228789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18574704879867275513638385 13931028659900456635228789)
                    ·
                      refine ⟨1306033936865667809552699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13931028659900456635228789 1306033936865667809552699)
                      ·
                        rfl

theorem cell23_2543492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_2543492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543492 prefixEnd_2543492 := by exact prefixLift 2543492
  have htrace : WordTrace (prefixWord ++ tailWord_2543492) baseStart_2543492 baseEnd_2543492 := by
    simpa [prefixWord, tailWord_2543492, baseEnd_2543492] using wordTrace_append hprefix tailTrace_2543492
  have hstable : (prefixWord ++ tailWord_2543492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543492).length < 2 ^ (prefixWord ++ tailWord_2543492).sum := by decide
  have hdescent : baseEnd_2543492 < baseStart_2543492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543506 : List Nat := [3, 2, 3, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_2543506 : Nat := 118140960795 + 2543506 * 2 ^ 59
def prefixEnd_2543506 : Nat := 4983230072969 + 3 ^ 40 * 2543506 * 2
def baseEnd_2543506 : Nat := 1306041125594830754777635

theorem tailTrace_2543506 : CollatzResearch.WordTrace tailWord_2543506 prefixEnd_2543506 1306041125594830754777635 := by
  unfold tailWord_2543506
  simp only [CollatzResearch.WordTrace]
  refine ⟨23192321280829908271464593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61846190082213088723905581 23192321280829908271464593)
  ·
    refine ⟨17394240960622431203598445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23192321280829908271464593 17394240960622431203598445)
    ·
      refine ⟨6522840360233411701349417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17394240960622431203598445 6522840360233411701349417)
      ·
        refine ⟨4892130270175058776012063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6522840360233411701349417 4892130270175058776012063)
        ·
          refine ⟨7338195405262588164018095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4892130270175058776012063 7338195405262588164018095)
          ·
            refine ⟨11007293107893882246027143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7338195405262588164018095 11007293107893882246027143)
            ·
              refine ⟨16510939661840823369040715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11007293107893882246027143 16510939661840823369040715)
              ·
                refine ⟨24766409492761235053561073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16510939661840823369040715 24766409492761235053561073)
                ·
                  refine ⟨18574807119570926290170805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24766409492761235053561073 18574807119570926290170805)
                  ·
                    refine ⟨1741388167459774339703513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18574807119570926290170805 1741388167459774339703513)
                    ·
                      refine ⟨1306041125594830754777635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1741388167459774339703513 1306041125594830754777635)
                      ·
                        rfl

theorem cell23_2543506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_2543506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543506 prefixEnd_2543506 := by exact prefixLift 2543506
  have htrace : WordTrace (prefixWord ++ tailWord_2543506) baseStart_2543506 baseEnd_2543506 := by
    simpa [prefixWord, tailWord_2543506, baseEnd_2543506] using wordTrace_append hprefix tailTrace_2543506
  have hstable : (prefixWord ++ tailWord_2543506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543506).length < 2 ^ (prefixWord ++ tailWord_2543506).sum := by decide
  have hdescent : baseEnd_2543506 < baseStart_2543506 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543562 : List Nat := [3, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6]
def baseStart_2543562 : Nat := 118140960795 + 2543562 * 2 ^ 59
def prefixEnd_2543562 : Nat := 4983230072969 + 3 ^ 40 * 2543562 * 2
def baseEnd_2543562 : Nat := 1306069880511482535677377

theorem tailTrace_2543562 : CollatzResearch.WordTrace tailWord_2543562 prefixEnd_2543562 1306069880511482535677377 := by
  unfold tailWord_2543562
  simp only [CollatzResearch.WordTrace]
  refine ⟨23192831902779188662474235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61847551740744503099931293 23192831902779188662474235)
  ·
    refine ⟨34789247854168782993711353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23192831902779188662474235 34789247854168782993711353)
    ·
      refine ⟨26091935890626587245283515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34789247854168782993711353 26091935890626587245283515)
      ·
        refine ⟨39137903835939880867925273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26091935890626587245283515 39137903835939880867925273)
        ·
          refine ⟨29353427876954910650943955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39137903835939880867925273 29353427876954910650943955)
          ·
            refine ⟨44030141815432365976415933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29353427876954910650943955 44030141815432365976415933)
            ·
              refine ⟨16511303180787137241155975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44030141815432365976415933 16511303180787137241155975)
              ·
                refine ⟨24766954771180705861733963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16511303180787137241155975 24766954771180705861733963)
                ·
                  refine ⟨37150432156771058792600945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24766954771180705861733963 37150432156771058792600945)
                  ·
                    refine ⟨27862824117578294094450709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37150432156771058792600945 27862824117578294094450709)
                    ·
                      refine ⟨1306069880511482535677377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27862824117578294094450709 1306069880511482535677377)
                      ·
                        rfl

theorem cell23_2543562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_2543562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543562 prefixEnd_2543562 := by exact prefixLift 2543562
  have htrace : WordTrace (prefixWord ++ tailWord_2543562) baseStart_2543562 baseEnd_2543562 := by
    simpa [prefixWord, tailWord_2543562, baseEnd_2543562] using wordTrace_append hprefix tailTrace_2543562
  have hstable : (prefixWord ++ tailWord_2543562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543562).length < 2 ^ (prefixWord ++ tailWord_2543562).sum := by decide
  have hdescent : baseEnd_2543562 < baseStart_2543562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543597 : List Nat := [1, 5, 1, 4, 1, 2, 1, 3, 1, 4]
def baseStart_2543597 : Nat := 118140960795 + 2543597 * 2 ^ 59
def prefixEnd_2543597 : Nat := 4983230072969 + 3 ^ 40 * 2543597 * 2
def baseEnd_2543597 : Nat := 435362617444796632913239

theorem tailTrace_2543597 : CollatzResearch.WordTrace tailWord_2543597 prefixEnd_2543597 435362617444796632913239 := by
  unfold tailWord_2543597
  simp only [CollatzResearch.WordTrace]
  refine ⟨92772604165989955627421045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61848402777326637084947363 92772604165989955627421045)
  ·
    refine ⟨8697431640561558340070723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92772604165989955627421045 8697431640561558340070723)
    ·
      refine ⟨13046147460842337510106085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8697431640561558340070723 13046147460842337510106085)
      ·
        refine ⟨2446152648907938283144891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13046147460842337510106085 2446152648907938283144891)
        ·
          refine ⟨3669228973361907424717337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446152648907938283144891 3669228973361907424717337)
          ·
            refine ⟨2751921730021430568538003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3669228973361907424717337 2751921730021430568538003)
            ·
              refine ⟨4127882595032145852807005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2751921730021430568538003 4127882595032145852807005)
              ·
                refine ⟨1547955973137054694802627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4127882595032145852807005 1547955973137054694802627)
                ·
                  refine ⟨2321933959705582042203941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1547955973137054694802627 2321933959705582042203941)
                  ·
                    refine ⟨435362617444796632913239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2321933959705582042203941 435362617444796632913239)
                    ·
                      rfl

theorem cell23_2543597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 1, 4].length) (baseStart_2543597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543597 prefixEnd_2543597 := by exact prefixLift 2543597
  have htrace : WordTrace (prefixWord ++ tailWord_2543597) baseStart_2543597 baseEnd_2543597 := by
    simpa [prefixWord, tailWord_2543597, baseEnd_2543597] using wordTrace_append hprefix tailTrace_2543597
  have hstable : (prefixWord ++ tailWord_2543597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543597).length < 2 ^ (prefixWord ++ tailWord_2543597).sum := by decide
  have hdescent : baseEnd_2543597 < baseStart_2543597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543693 : List Nat := [1, 6, 1, 1, 1, 1, 4, 1, 1, 3, 3]
def baseStart_2543693 : Nat := 118140960795 + 2543693 * 2 ^ 59
def prefixEnd_2543693 : Nat := 4983230072969 + 3 ^ 40 * 2543693 * 2
def baseEnd_2543693 : Nat := 1306137146477221523139275

theorem tailTrace_2543693 : CollatzResearch.WordTrace tailWord_2543693 prefixEnd_2543693 1306137146477221523139275 := by
  unfold tailWord_2543693
  simp only [CollatzResearch.WordTrace]
  refine ⟨92776105573642164022915733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61850737049094776015277155 92776105573642164022915733)
  ·
    refine ⟨4348879948764476438574175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92776105573642164022915733 4348879948764476438574175)
    ·
      refine ⟨6523319923146714657861263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4348879948764476438574175 6523319923146714657861263)
      ·
        refine ⟨9784979884720071986791895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6523319923146714657861263 9784979884720071986791895)
        ·
          refine ⟨14677469827080107980187843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9784979884720071986791895 14677469827080107980187843)
          ·
            refine ⟨22016204740620161970281765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14677469827080107980187843 22016204740620161970281765)
            ·
              refine ⟨4128038388866280369427831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22016204740620161970281765 4128038388866280369427831)
              ·
                refine ⟨6192057583299420554141747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128038388866280369427831 6192057583299420554141747)
                ·
                  refine ⟨9288086374949130831212621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6192057583299420554141747 9288086374949130831212621)
                  ·
                    refine ⟨3483032390605924061704733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9288086374949130831212621 3483032390605924061704733)
                    ·
                      refine ⟨1306137146477221523139275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3483032390605924061704733 1306137146477221523139275)
                      ·
                        rfl

theorem cell23_2543693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_2543693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543693 prefixEnd_2543693 := by exact prefixLift 2543693
  have htrace : WordTrace (prefixWord ++ tailWord_2543693) baseStart_2543693 baseEnd_2543693 := by
    simpa [prefixWord, tailWord_2543693, baseEnd_2543693] using wordTrace_append hprefix tailTrace_2543693
  have hstable : (prefixWord ++ tailWord_2543693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543693).length < 2 ^ (prefixWord ++ tailWord_2543693).sum := by decide
  have hdescent : baseEnd_2543693 < baseStart_2543693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543714 : List Nat := [3, 3, 2, 2, 3, 1, 2, 1, 1, 2, 3]
def baseStart_2543714 : Nat := 118140960795 + 2543714 * 2 ^ 59
def prefixEnd_2543714 : Nat := 4983230072969 + 3 ^ 40 * 2543714 * 2
def baseEnd_2543714 : Nat := 1306147929570965940976679

theorem tailTrace_2543714 : CollatzResearch.WordTrace tailWord_2543714 prefixEnd_2543714 1306147929570965940976679 := by
  unfold tailWord_2543714
  simp only [CollatzResearch.WordTrace]
  refine ⟨23194217876641521152357549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61851247671044056406286797 23194217876641521152357549)
  ·
    refine ⟨8697831703740570432134081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23194217876641521152357549 8697831703740570432134081)
    ·
      refine ⟨6523373777805427824100561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8697831703740570432134081 6523373777805427824100561)
      ·
        refine ⟨4892530333354070868075421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6523373777805427824100561 4892530333354070868075421)
        ·
          refine ⟨1834698875007776575528283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4892530333354070868075421 1834698875007776575528283)
          ·
            refine ⟨2752048312511664863292425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834698875007776575528283 2752048312511664863292425)
            ·
              refine ⟨2064036234383748647469319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2752048312511664863292425 2064036234383748647469319)
              ·
                refine ⟨3096054351575622971203979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2064036234383748647469319 3096054351575622971203979)
                ·
                  refine ⟨4644081527363434456805969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3096054351575622971203979 4644081527363434456805969)
                  ·
                    refine ⟨3483061145522575842604477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4644081527363434456805969 3483061145522575842604477)
                    ·
                      refine ⟨1306147929570965940976679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3483061145522575842604477 1306147929570965940976679)
                      ·
                        rfl

theorem cell23_2543714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_2543714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543714 prefixEnd_2543714 := by exact prefixLift 2543714
  have htrace : WordTrace (prefixWord ++ tailWord_2543714) baseStart_2543714 baseEnd_2543714 := by
    simpa [prefixWord, tailWord_2543714, baseEnd_2543714] using wordTrace_append hprefix tailTrace_2543714
  have hstable : (prefixWord ++ tailWord_2543714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543714).length < 2 ^ (prefixWord ++ tailWord_2543714).sum := by decide
  have hdescent : baseEnd_2543714 < baseStart_2543714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543719 : List Nat := [1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 5]
def baseStart_2543719 : Nat := 118140960795 + 2543719 * 2 ^ 59
def prefixEnd_2543719 : Nat := 4983230072969 + 3 ^ 40 * 2543719 * 2
def baseEnd_2543719 : Nat := 1306150496974238421414155

theorem tailTrace_2543719 : CollatzResearch.WordTrace tailWord_2543719 prefixEnd_2543719 1306150496974238421414155 := by
  unfold tailWord_2543719
  simp only [CollatzResearch.WordTrace]
  refine ⟨92777053871547970463362211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61851369247698646975574807 92777053871547970463362211)
  ·
    refine ⟨139165580807321955695043317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92777053871547970463362211 139165580807321955695043317)
    ·
      refine ⟨13046773200686433346410311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139165580807321955695043317 13046773200686433346410311)
      ·
        refine ⟨19570159801029650019615467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13046773200686433346410311 19570159801029650019615467)
        ·
          refine ⟨29355239701544475029423201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19570159801029650019615467 29355239701544475029423201)
          ·
            refine ⟨22016429776158356272067401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29355239701544475029423201 22016429776158356272067401)
            ·
              refine ⟨16512322332118767204050551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22016429776158356272067401 16512322332118767204050551)
              ·
                refine ⟨24768483498178150806075827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16512322332118767204050551 24768483498178150806075827)
                ·
                  refine ⟨37152725247267226209113741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24768483498178150806075827 37152725247267226209113741)
                  ·
                    refine ⟨13932271967725209828417653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37152725247267226209113741 13932271967725209828417653)
                    ·
                      refine ⟨1306150496974238421414155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13932271967725209828417653 1306150496974238421414155)
                      ·
                        rfl

theorem cell23_2543719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_2543719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543719 prefixEnd_2543719 := by exact prefixLift 2543719
  have htrace : WordTrace (prefixWord ++ tailWord_2543719) baseStart_2543719 baseEnd_2543719 := by
    simpa [prefixWord, tailWord_2543719, baseEnd_2543719] using wordTrace_append hprefix tailTrace_2543719
  have hstable : (prefixWord ++ tailWord_2543719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543719).length < 2 ^ (prefixWord ++ tailWord_2543719).sum := by decide
  have hdescent : baseEnd_2543719 < baseStart_2543719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543729 : List Nat := [1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_2543729 : Nat := 118140960795 + 2543729 * 2 ^ 59
def prefixEnd_2543729 : Nat := 4983230072969 + 3 ^ 40 * 2543729 * 2
def baseEnd_2543729 : Nat := 1306155631780783382289109

theorem tailTrace_2543729 : CollatzResearch.WordTrace tailWord_2543729 prefixEnd_2543729 1306155631780783382289109 := by
  unfold tailWord_2543729
  simp only [CollatzResearch.WordTrace]
  refine ⟨92777418601511742171226241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61851612401007828114150827 92777418601511742171226241)
  ·
    refine ⟨69583063951133806628419681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92777418601511742171226241 69583063951133806628419681)
    ·
      refine ⟨52187297963350354971314761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69583063951133806628419681 52187297963350354971314761)
      ·
        refine ⟨39140473472512766228486071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52187297963350354971314761 39140473472512766228486071)
        ·
          refine ⟨58710710208769149342729107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39140473472512766228486071 58710710208769149342729107)
          ·
            refine ⟨88066065313153724014093661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58710710208769149342729107 88066065313153724014093661)
            ·
              refine ⟨33024774492432646505285123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88066065313153724014093661 33024774492432646505285123)
              ·
                refine ⟨49537161738648969757927685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33024774492432646505285123 49537161738648969757927685)
                ·
                  refine ⟨9288217825996681829611441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49537161738648969757927685 9288217825996681829611441)
                  ·
                    refine ⟨6966163369497511372208581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9288217825996681829611441 6966163369497511372208581)
                    ·
                      refine ⟨1306155631780783382289109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6966163369497511372208581 1306155631780783382289109)
                      ·
                        rfl

theorem cell23_2543729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_2543729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543729 prefixEnd_2543729 := by exact prefixLift 2543729
  have htrace : WordTrace (prefixWord ++ tailWord_2543729) baseStart_2543729 baseEnd_2543729 := by
    simpa [prefixWord, tailWord_2543729, baseEnd_2543729] using wordTrace_append hprefix tailTrace_2543729
  have hstable : (prefixWord ++ tailWord_2543729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543729).length < 2 ^ (prefixWord ++ tailWord_2543729).sum := by decide
  have hdescent : baseEnd_2543729 < baseStart_2543729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543769 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 6, 5]
def baseStart_2543769 : Nat := 118140960795 + 2543769 * 2 ^ 59
def prefixEnd_2543769 : Nat := 4983230072969 + 3 ^ 40 * 2543769 * 2
def baseEnd_2543769 : Nat := 435392057002321075262975

theorem tailTrace_2543769 : CollatzResearch.WordTrace tailWord_2543769 prefixEnd_2543769 435392057002321075262975 := by
  unfold tailWord_2543769
  simp only [CollatzResearch.WordTrace]
  refine ⟨92778877521366829002682361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61852585014244552668454907 92778877521366829002682361)
  ·
    refine ⟨69584158141025121752011771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92778877521366829002682361 69584158141025121752011771)
    ·
      refine ⟨104376237211537682628017657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69584158141025121752011771 104376237211537682628017657)
      ·
        refine ⟨78282177908653261971013243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104376237211537682628017657 78282177908653261971013243)
        ·
          refine ⟨117423266862979892956519865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78282177908653261971013243 117423266862979892956519865)
          ·
            refine ⟨88067450147234919717389899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117423266862979892956519865 88067450147234919717389899)
            ·
              refine ⟨132101175220852379576084849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88067450147234919717389899 132101175220852379576084849)
              ·
                refine ⟨99075881415639284682063637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 132101175220852379576084849 99075881415639284682063637)
                ·
                  refine ⟨4644181941358091469471733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99075881415639284682063637 4644181941358091469471733)
                  ·
                    refine ⟨435392057002321075262975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4644181941358091469471733 435392057002321075262975)
                    ·
                      rfl

theorem cell23_2543769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 6, 5].length) (baseStart_2543769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543769 prefixEnd_2543769 := by exact prefixLift 2543769
  have htrace : WordTrace (prefixWord ++ tailWord_2543769) baseStart_2543769 baseEnd_2543769 := by
    simpa [prefixWord, tailWord_2543769, baseEnd_2543769] using wordTrace_append hprefix tailTrace_2543769
  have hstable : (prefixWord ++ tailWord_2543769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543769).length < 2 ^ (prefixWord ++ tailWord_2543769).sum := by decide
  have hdescent : baseEnd_2543769 < baseStart_2543769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543773 : List Nat := [1, 4, 2, 1, 1, 3, 3, 3, 5]
def baseStart_2543773 : Nat := 118140960795 + 2543773 * 2 ^ 59
def prefixEnd_2543773 : Nat := 4983230072969 + 3 ^ 40 * 2543773 * 2
def baseEnd_2543773 : Nat := 145130913881064578904323

theorem tailTrace_2543773 : CollatzResearch.WordTrace tailWord_2543773 prefixEnd_2543773 145130913881064578904323 := by
  unfold tailWord_2543773
  simp only [CollatzResearch.WordTrace]
  refine ⟨92779023413352337685827973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61852682275568225123885315 92779023413352337685827973)
  ·
    refine ⟨17396066890003563316092745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 92779023413352337685827973 17396066890003563316092745)
    ·
      refine ⟨13047050167502672487069559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17396066890003563316092745 13047050167502672487069559)
      ·
        refine ⟨19570575251254008730604339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13047050167502672487069559 19570575251254008730604339)
        ·
          refine ⟨29355862876881013095906509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19570575251254008730604339 29355862876881013095906509)
          ·
            refine ⟨11008448578830379910964941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29355862876881013095906509 11008448578830379910964941)
            ·
              refine ⟨4128168217061392466611853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11008448578830379910964941 4128168217061392466611853)
              ·
                refine ⟨1548063081398022174979445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4128168217061392466611853 1548063081398022174979445)
                ·
                  refine ⟨145130913881064578904323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1548063081398022174979445 145130913881064578904323)
                  ·
                    rfl

theorem cell23_2543773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_2543773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543773 prefixEnd_2543773 := by exact prefixLift 2543773
  have htrace : WordTrace (prefixWord ++ tailWord_2543773) baseStart_2543773 baseEnd_2543773 := by
    simpa [prefixWord, tailWord_2543773, baseEnd_2543773] using wordTrace_append hprefix tailTrace_2543773
  have hstable : (prefixWord ++ tailWord_2543773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543773).length < 2 ^ (prefixWord ++ tailWord_2543773).sum := by decide
  have hdescent : baseEnd_2543773 < baseStart_2543773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543816 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 5, 4]
def baseStart_2543816 : Nat := 118140960795 + 2543816 * 2 ^ 59
def prefixEnd_2543816 : Nat := 4983230072969 + 3 ^ 40 * 2543816 * 2
def baseEnd_2543816 : Nat := 435400101532574847300403

theorem tailTrace_2543816 : CollatzResearch.WordTrace tailWord_2543816 prefixEnd_2543816 435400101532574847300403 := by
  unfold tailWord_2543816
  simp only [CollatzResearch.WordTrace]
  refine ⟨46390295876098278014821651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61853727834797704019762201 46390295876098278014821651)
  ·
    refine ⟨69585443814147417022232477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46390295876098278014821651 69585443814147417022232477)
    ·
      refine ⟨26094541430305281383337179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69585443814147417022232477 26094541430305281383337179)
      ·
        refine ⟨39141812145457922075005769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26094541430305281383337179 39141812145457922075005769)
        ·
          refine ⟨29356359109093441556254327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39141812145457922075005769 29356359109093441556254327)
          ·
            refine ⟨44034538663640162334381491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29356359109093441556254327 44034538663640162334381491)
            ·
              refine ⟨66051807995460243501572237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44034538663640162334381491 66051807995460243501572237)
              ·
                refine ⟨24769427998297591313089589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66051807995460243501572237 24769427998297591313089589)
                ·
                  refine ⟨2322133874840399185602149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24769427998297591313089589 2322133874840399185602149)
                  ·
                    refine ⟨435400101532574847300403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2322133874840399185602149 435400101532574847300403)
                    ·
                      rfl

theorem cell23_2543816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5, 4].length) (baseStart_2543816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543816 prefixEnd_2543816 := by exact prefixLift 2543816
  have htrace : WordTrace (prefixWord ++ tailWord_2543816) baseStart_2543816 baseEnd_2543816 := by
    simpa [prefixWord, tailWord_2543816, baseEnd_2543816] using wordTrace_append hprefix tailTrace_2543816
  have hstable : (prefixWord ++ tailWord_2543816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543816).length < 2 ^ (prefixWord ++ tailWord_2543816).sum := by decide
  have hdescent : baseEnd_2543816 < baseStart_2543816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543820 : List Nat := [2, 2, 1, 6, 1, 1, 2, 1, 2, 5]
def baseStart_2543820 : Nat := 118140960795 + 2543820 * 2 ^ 59
def prefixEnd_2543820 : Nat := 4983230072969 + 3 ^ 40 * 2543820 * 2
def baseEnd_2543820 : Nat := 435400786173447508750397

theorem tailTrace_2543820 : CollatzResearch.WordTrace tailWord_2543820 prefixEnd_2543820 435400786173447508750397 := by
  unfold tailWord_2543820
  simp only [CollatzResearch.WordTrace]
  refine ⟨46390368822091032356394457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61853825096121376475192609 46390368822091032356394457)
  ·
    refine ⟨34792776616568274267295843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46390368822091032356394457 34792776616568274267295843)
    ·
      refine ⟨52189164924852411400943765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34792776616568274267295843 52189164924852411400943765)
      ·
        refine ⟨2446367105852456784419239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 52189164924852411400943765 2446367105852456784419239)
        ·
          refine ⟨3669550658778685176628859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2446367105852456784419239 3669550658778685176628859)
          ·
            refine ⟨5504325988168027764943289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3669550658778685176628859 5504325988168027764943289)
            ·
              refine ⟨4128244491126020823707467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5504325988168027764943289 4128244491126020823707467)
              ·
                refine ⟨6192366736689031235561201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4128244491126020823707467 6192366736689031235561201)
                ·
                  refine ⟨4644275052516773426670901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6192366736689031235561201 4644275052516773426670901)
                  ·
                    refine ⟨435400786173447508750397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4644275052516773426670901 435400786173447508750397)
                    ·
                      rfl

theorem cell23_2543820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 1, 2, 1, 2, 5].length) (baseStart_2543820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543820 prefixEnd_2543820 := by exact prefixLift 2543820
  have htrace : WordTrace (prefixWord ++ tailWord_2543820) baseStart_2543820 baseEnd_2543820 := by
    simpa [prefixWord, tailWord_2543820, baseEnd_2543820] using wordTrace_append hprefix tailTrace_2543820
  have hstable : (prefixWord ++ tailWord_2543820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543820).length < 2 ^ (prefixWord ++ tailWord_2543820).sum := by decide
  have hdescent : baseEnd_2543820 < baseStart_2543820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543849 : List Nat := [1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 8]
def baseStart_2543849 : Nat := 118140960795 + 2543849 * 2 ^ 59
def prefixEnd_2543849 : Nat := 4983230072969 + 3 ^ 40 * 2543849 * 2
def baseEnd_2543849 : Nat := 1306217249459322912788557

theorem tailTrace_2543849 : CollatzResearch.WordTrace tailWord_2543849 prefixEnd_2543849 1306217249459322912788557 := by
  unfold tailWord_2543849
  simp only [CollatzResearch.WordTrace]
  refine ⟨92781795361077002665594601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61854530240718001777063067 92781795361077002665594601)
  ·
    refine ⟨69586346520807751999195951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92781795361077002665594601 69586346520807751999195951)
    ·
      refine ⟨104379519781211627998793927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69586346520807751999195951 104379519781211627998793927)
      ·
        refine ⟨156569279671817441998190891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104379519781211627998793927 156569279671817441998190891)
        ·
          refine ⟨234853919507726162997286337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156569279671817441998190891 234853919507726162997286337)
          ·
            refine ⟨176140439630794622247964753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 234853919507726162997286337 176140439630794622247964753)
            ·
              refine ⟨132105329723095966685973565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176140439630794622247964753 132105329723095966685973565)
              ·
                refine ⟨49539498646160987507240087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132105329723095966685973565 49539498646160987507240087)
                ·
                  refine ⟨74309247969241481260860131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49539498646160987507240087 74309247969241481260860131)
                  ·
                    refine ⟨111463871953862221891290197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74309247969241481260860131 111463871953862221891290197)
                    ·
                      refine ⟨1306217249459322912788557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 111463871953862221891290197 1306217249459322912788557)
                      ·
                        rfl

theorem cell23_2543849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 3, 1, 1, 8].length) (baseStart_2543849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543849 prefixEnd_2543849 := by exact prefixLift 2543849
  have htrace : WordTrace (prefixWord ++ tailWord_2543849) baseStart_2543849 baseEnd_2543849 := by
    simpa [prefixWord, tailWord_2543849, baseEnd_2543849] using wordTrace_append hprefix tailTrace_2543849
  have hstable : (prefixWord ++ tailWord_2543849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543849).length < 2 ^ (prefixWord ++ tailWord_2543849).sum := by decide
  have hdescent : baseEnd_2543849 < baseStart_2543849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543850 : List Nat := [3, 1, 3, 1, 1, 2, 3, 4, 1, 4]
def baseStart_2543850 : Nat := 118140960795 + 2543850 * 2 ^ 59
def prefixEnd_2543850 : Nat := 4983230072969 + 3 ^ 40 * 2543850 * 2
def baseEnd_2543850 : Nat := 435405920979992469625351

theorem tailTrace_2543850 : CollatzResearch.WordTrace tailWord_2543850 prefixEnd_2543850 435405920979992469625351 := by
  unfold tailWord_2543850
  simp only [CollatzResearch.WordTrace]
  refine ⟨23195457958518344959095251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61854554556048919890920669 23195457958518344959095251)
  ·
    refine ⟨34793186937777517438642877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23195457958518344959095251 34793186937777517438642877)
    ·
      refine ⟨13047445101666569039491079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34793186937777517438642877 13047445101666569039491079)
      ·
        refine ⟨19571167652499853559236619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13047445101666569039491079 19571167652499853559236619)
        ·
          refine ⟨29356751478749780338854929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19571167652499853559236619 29356751478749780338854929)
          ·
            refine ⟨22017563609062335254141197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29356751478749780338854929 22017563609062335254141197)
            ·
              refine ⟨8256586353398375720302949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22017563609062335254141197 8256586353398375720302949)
              ·
                refine ⟨1548109941262195447556803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8256586353398375720302949 1548109941262195447556803)
                ·
                  refine ⟨2322164911893293171335205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548109941262195447556803 2322164911893293171335205)
                  ·
                    refine ⟨435405920979992469625351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2322164911893293171335205 435405920979992469625351)
                    ·
                      rfl

theorem cell23_2543850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_2543850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543850 prefixEnd_2543850 := by exact prefixLift 2543850
  have htrace : WordTrace (prefixWord ++ tailWord_2543850) baseStart_2543850 baseEnd_2543850 := by
    simpa [prefixWord, tailWord_2543850, baseEnd_2543850] using wordTrace_append hprefix tailTrace_2543850
  have hstable : (prefixWord ++ tailWord_2543850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543850).length < 2 ^ (prefixWord ++ tailWord_2543850).sum := by decide
  have hdescent : baseEnd_2543850 < baseStart_2543850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543883 : List Nat := [1, 1, 1, 1, 5, 2, 3, 1, 1, 5, 2]
def baseStart_2543883 : Nat := 118140960795 + 2543883 * 2 ^ 59
def prefixEnd_2543883 : Nat := 4983230072969 + 3 ^ 40 * 2543883 * 2
def baseEnd_2543883 : Nat := 1306234707801575779763401

theorem tailTrace_2543883 : CollatzResearch.WordTrace tailWord_2543883 prefixEnd_2543883 1306234707801575779763401 := by
  unfold tailWord_2543883
  simp only [CollatzResearch.WordTrace]
  refine ⟨92783035442953826472332303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61855356961969217648221535 92783035442953826472332303)
  ·
    refine ⟨139174553164430739708498455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92783035442953826472332303 139174553164430739708498455)
    ·
      refine ⟨208761829746646109562747683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139174553164430739708498455 208761829746646109562747683)
      ·
        refine ⟨313142744619969164344121525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208761829746646109562747683 313142744619969164344121525)
        ·
          refine ⟨29357132308122109157261393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 313142744619969164344121525 29357132308122109157261393)
          ·
            refine ⟨22017849231091581867946045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29357132308122109157261393 22017849231091581867946045)
            ·
              refine ⟨8256693461659343200479767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22017849231091581867946045 8256693461659343200479767)
              ·
                refine ⟨12385040192489014800719651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8256693461659343200479767 12385040192489014800719651)
                ·
                  refine ⟨18577560288733522201079477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12385040192489014800719651 18577560288733522201079477)
                  ·
                    refine ⟨1741646277068767706351201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18577560288733522201079477 1741646277068767706351201)
                    ·
                      refine ⟨1306234707801575779763401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1741646277068767706351201 1306234707801575779763401)
                      ·
                        rfl

theorem cell23_2543883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 5, 2].length) (baseStart_2543883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543883 prefixEnd_2543883 := by exact prefixLift 2543883
  have htrace : WordTrace (prefixWord ++ tailWord_2543883) baseStart_2543883 baseEnd_2543883 := by
    simpa [prefixWord, tailWord_2543883, baseEnd_2543883] using wordTrace_append hprefix tailTrace_2543883
  have hstable : (prefixWord ++ tailWord_2543883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543883).length < 2 ^ (prefixWord ++ tailWord_2543883).sum := by decide
  have hdescent : baseEnd_2543883 < baseStart_2543883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543916 : List Nat := [2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_2543916 : Nat := 118140960795 + 2543916 * 2 ^ 59
def prefixEnd_2543916 : Nat := 4983230072969 + 3 ^ 40 * 2543916 * 2
def baseEnd_2543916 : Nat := 1306251652663174150650749

theorem tailTrace_2543916 : CollatzResearch.WordTrace tailWord_2543916 prefixEnd_2543916 1306251652663174150650749 := by
  unfold tailWord_2543916
  simp only [CollatzResearch.WordTrace]
  refine ⟨46392119525917136554141801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61856159367889515405522401 46392119525917136554141801)
  ·
    refine ⟨34794089644437852415606351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46392119525917136554141801 34794089644437852415606351)
    ·
      refine ⟨52191134466656778623409527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34794089644437852415606351 52191134466656778623409527)
      ·
        refine ⟨78286701699985167935114291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52191134466656778623409527 78286701699985167935114291)
        ·
          refine ⟨117430052549977751902671437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78286701699985167935114291 117430052549977751902671437)
          ·
            refine ⟨44036269706241656963501789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117430052549977751902671437 44036269706241656963501789)
            ·
              refine ⟨16513601139840621361313171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44036269706241656963501789 16513601139840621361313171)
              ·
                refine ⟨24770401709760932041969757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16513601139840621361313171 24770401709760932041969757)
                ·
                  refine ⟨9288900641160349515738659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24770401709760932041969757 9288900641160349515738659)
                  ·
                    refine ⟨13933350961740524273607989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9288900641160349515738659 13933350961740524273607989)
                    ·
                      refine ⟨1306251652663174150650749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13933350961740524273607989 1306251652663174150650749)
                      ·
                        rfl

theorem cell23_2543916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_2543916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543916 prefixEnd_2543916 := by exact prefixLift 2543916
  have htrace : WordTrace (prefixWord ++ tailWord_2543916) baseStart_2543916 baseEnd_2543916 := by
    simpa [prefixWord, tailWord_2543916, baseEnd_2543916] using wordTrace_append hprefix tailTrace_2543916
  have hstable : (prefixWord ++ tailWord_2543916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543916).length < 2 ^ (prefixWord ++ tailWord_2543916).sum := by decide
  have hdescent : baseEnd_2543916 < baseStart_2543916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543930 : List Nat := [3, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4]
def baseStart_2543930 : Nat := 118140960795 + 2543930 * 2 ^ 59
def prefixEnd_2543930 : Nat := 4983230072969 + 3 ^ 40 * 2543930 * 2
def baseEnd_2543930 : Nat := 1306258841392337095875685

theorem tailTrace_2543930 : CollatzResearch.WordTrace tailWord_2543930 prefixEnd_2543930 1306258841392337095875685 := by
  unfold tailWord_2543930
  simp only [CollatzResearch.WordTrace]
  refine ⟨23196187418445888374823311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61856499782522368999528829 23196187418445888374823311)
  ·
    refine ⟨34794281127668832562234967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23196187418445888374823311 34794281127668832562234967)
    ·
      refine ⟨52191421691503248843352451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34794281127668832562234967 52191421691503248843352451)
      ·
        refine ⟨78287132537254873265028677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52191421691503248843352451 78287132537254873265028677)
        ·
          refine ⟨14678837350735288737192877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78287132537254873265028677 14678837350735288737192877)
          ·
            refine ⟨5504564006525733276447329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14678837350735288737192877 5504564006525733276447329)
            ·
              refine ⟨4128423004894299957335497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5504564006525733276447329 4128423004894299957335497)
              ·
                refine ⟨3096317253670724968001623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128423004894299957335497 3096317253670724968001623)
                ·
                  refine ⟨4644475880506087452002435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3096317253670724968001623 4644475880506087452002435)
                  ·
                    refine ⟨6966713820759131178003653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4644475880506087452002435 6966713820759131178003653)
                    ·
                      refine ⟨1306258841392337095875685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6966713820759131178003653 1306258841392337095875685)
                      ·
                        rfl

theorem cell23_2543930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 2, 2, 1, 1, 4].length) (baseStart_2543930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543930 prefixEnd_2543930 := by exact prefixLift 2543930
  have htrace : WordTrace (prefixWord ++ tailWord_2543930) baseStart_2543930 baseEnd_2543930 := by
    simpa [prefixWord, tailWord_2543930, baseEnd_2543930] using wordTrace_append hprefix tailTrace_2543930
  have hstable : (prefixWord ++ tailWord_2543930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543930).length < 2 ^ (prefixWord ++ tailWord_2543930).sum := by decide
  have hdescent : baseEnd_2543930 < baseStart_2543930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543947 : List Nat := [1, 1, 1, 1, 3, 1, 1, 9, 1, 2, 2]
def baseStart_2543947 : Nat := 118140960795 + 2543947 * 2 ^ 59
def prefixEnd_2543947 : Nat := 4983230072969 + 3 ^ 40 * 2543947 * 2
def baseEnd_2543947 : Nat := 1306267570563463529363107

theorem tailTrace_2543947 : CollatzResearch.WordTrace tailWord_2543947 prefixEnd_2543947 1306267570563463529363107 := by
  unfold tailWord_2543947
  simp only [CollatzResearch.WordTrace]
  refine ⟨92785369714721965402662095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61856913143147976935108063 92785369714721965402662095)
  ·
    refine ⟨139178054572082948103993143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92785369714721965402662095 139178054572082948103993143)
    ·
      refine ⟨208767081858124422155989715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139178054572082948103993143 208767081858124422155989715)
      ·
        refine ⟨313150622787186633233984573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208767081858124422155989715 313150622787186633233984573)
        ·
          refine ⟨117431483545194987462744215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313150622787186633233984573 117431483545194987462744215)
          ·
            refine ⟨176147225317792481194116323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117431483545194987462744215 176147225317792481194116323)
            ·
              refine ⟨264220837976688721791174485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176147225317792481194116323 264220837976688721791174485)
              ·
                refine ⟨1548168972519660479245163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 264220837976688721791174485 1548168972519660479245163)
                ·
                  refine ⟨2322253458779490718867745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548168972519660479245163 2322253458779490718867745)
                  ·
                    refine ⟨1741690094084618039150809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2322253458779490718867745 1741690094084618039150809)
                    ·
                      refine ⟨1306267570563463529363107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1741690094084618039150809 1306267570563463529363107)
                      ·
                        rfl

theorem cell23_2543947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 9, 1, 2, 2].length) (baseStart_2543947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543947 prefixEnd_2543947 := by exact prefixLift 2543947
  have htrace : WordTrace (prefixWord ++ tailWord_2543947) baseStart_2543947 baseEnd_2543947 := by
    simpa [prefixWord, tailWord_2543947, baseEnd_2543947] using wordTrace_append hprefix tailTrace_2543947
  have hstable : (prefixWord ++ tailWord_2543947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543947).length < 2 ^ (prefixWord ++ tailWord_2543947).sum := by decide
  have hdescent : baseEnd_2543947 < baseStart_2543947 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2543996 : List Nat := [2, 2, 2, 1, 1, 1, 2, 1, 3, 8]
def baseStart_2543996 : Nat := 118140960795 + 2543996 * 2 ^ 59
def prefixEnd_2543996 : Nat := 4983230072969 + 3 ^ 40 * 2543996 * 2
def baseEnd_2543996 : Nat := 435430910371844612550127

theorem tailTrace_2543996 : CollatzResearch.WordTrace tailWord_2543996 prefixEnd_2543996 435430910371844612550127 := by
  unfold tailWord_2543996
  simp only [CollatzResearch.WordTrace]
  refine ⟨46393578445772223385597921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61858104594362964514130561 46393578445772223385597921)
  ·
    refine ⟨34795183834329167539198441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46393578445772223385597921 34795183834329167539198441)
    ·
      refine ⟨26096387875746875654398831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34795183834329167539198441 26096387875746875654398831)
      ·
        refine ⟨39144581813620313481598247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26096387875746875654398831 39144581813620313481598247)
        ·
          refine ⟨58716872720430470222397371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39144581813620313481598247 58716872720430470222397371)
          ·
            refine ⟨88075309080645705333596057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58716872720430470222397371 88075309080645705333596057)
            ·
              refine ⟨66056481810484279000197043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88075309080645705333596057 66056481810484279000197043)
              ·
                refine ⟨99084722715726418500295565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66056481810484279000197043 99084722715726418500295565)
                ·
                  refine ⟨37156771018397406937610837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99084722715726418500295565 37156771018397406937610837)
                  ·
                    refine ⟨435430910371844612550127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37156771018397406937610837 435430910371844612550127)
                    ·
                      rfl

theorem cell23_2543996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_2543996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2543996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2543996 prefixEnd_2543996 := by exact prefixLift 2543996
  have htrace : WordTrace (prefixWord ++ tailWord_2543996) baseStart_2543996 baseEnd_2543996 := by
    simpa [prefixWord, tailWord_2543996, baseEnd_2543996] using wordTrace_append hprefix tailTrace_2543996
  have hstable : (prefixWord ++ tailWord_2543996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2543996).length < 2 ^ (prefixWord ++ tailWord_2543996).sum := by decide
  have hdescent : baseEnd_2543996 < baseStart_2543996 := by decide
  rcases family_descends (prefixWord ++ tailWord_2543996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544014 : List Nat := [4, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_2544014 : Nat := 118140960795 + 2544014 * 2 ^ 59
def prefixEnd_2544014 : Nat := 4983230072969 + 3 ^ 40 * 2544014 * 2
def baseEnd_2544014 : Nat := 1306301973767314767225299

theorem tailTrace_2544014 : CollatzResearch.WordTrace tailWord_2544014 prefixEnd_2544014 1306301973767314767225299 := by
  unfold tailWord_2544014
  simp only [CollatzResearch.WordTrace]
  refine ⟨11598476675684904480668887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61858542270319490563567397 11598476675684904480668887)
  ·
    refine ⟨17397715013527356721003331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11598476675684904480668887 17397715013527356721003331)
    ·
      refine ⟨26096572520291035081504997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17397715013527356721003331 26096572520291035081504997)
      ·
        refine ⟨4893107347554569077782187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26096572520291035081504997 4893107347554569077782187)
        ·
          refine ⟨7339661021331853616673281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893107347554569077782187 7339661021331853616673281)
          ·
            refine ⟨5504745765998890212504961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7339661021331853616673281 5504745765998890212504961)
            ·
              refine ⟨4128559324499167659378721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5504745765998890212504961 4128559324499167659378721)
              ·
                refine ⟨3096419493374375744534041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128559324499167659378721 3096419493374375744534041)
                ·
                  refine ⟨2322314620030781808400531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3096419493374375744534041 2322314620030781808400531)
                  ·
                    refine ⟨3483471930046172712600797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2322314620030781808400531 3483471930046172712600797)
                    ·
                      refine ⟨1306301973767314767225299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3483471930046172712600797 1306301973767314767225299)
                      ·
                        rfl

theorem cell23_2544014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_2544014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544014 prefixEnd_2544014 := by exact prefixLift 2544014
  have htrace : WordTrace (prefixWord ++ tailWord_2544014) baseStart_2544014 baseEnd_2544014 := by
    simpa [prefixWord, tailWord_2544014, baseEnd_2544014] using wordTrace_append hprefix tailTrace_2544014
  have hstable : (prefixWord ++ tailWord_2544014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544014).length < 2 ^ (prefixWord ++ tailWord_2544014).sum := by decide
  have hdescent : baseEnd_2544014 < baseStart_2544014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544023 : List Nat := [1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 3]
def baseStart_2544023 : Nat := 118140960795 + 2544023 * 2 ^ 59
def prefixEnd_2544023 : Nat := 4983230072969 + 3 ^ 40 * 2544023 * 2
def baseEnd_2544023 : Nat := 1306306595093205232012757

theorem tailTrace_2544023 : CollatzResearch.WordTrace tailWord_2544023 prefixEnd_2544023 1306306595093205232012757 := by
  unfold tailWord_2544023
  simp only [CollatzResearch.WordTrace]
  refine ⟨92788141662446630382428723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61858761108297753588285815 92788141662446630382428723)
  ·
    refine ⟨139182212493669945573643085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92788141662446630382428723 139182212493669945573643085)
    ·
      refine ⟨52193329685126229590116157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139182212493669945573643085 52193329685126229590116157)
      ·
        refine ⟨19572498631922336096293559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52193329685126229590116157 19572498631922336096293559)
        ·
          refine ⟨29358747947883504144440339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19572498631922336096293559 29358747947883504144440339)
          ·
            refine ⟨44038121921825256216660509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29358747947883504144440339 44038121921825256216660509)
            ·
              refine ⟨16514295720684471081247691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44038121921825256216660509 16514295720684471081247691)
              ·
                refine ⟨24771443581026706621871537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16514295720684471081247691 24771443581026706621871537)
                ·
                  refine ⟨18578582685770029966403653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24771443581026706621871537 18578582685770029966403653)
                  ·
                    refine ⟨3483484253581880618700685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18578582685770029966403653 3483484253581880618700685)
                    ·
                      refine ⟨1306306595093205232012757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3483484253581880618700685 1306306595093205232012757)
                      ·
                        rfl

theorem cell23_2544023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 4, 3].length) (baseStart_2544023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544023 prefixEnd_2544023 := by exact prefixLift 2544023
  have htrace : WordTrace (prefixWord ++ tailWord_2544023) baseStart_2544023 baseEnd_2544023 := by
    simpa [prefixWord, tailWord_2544023, baseEnd_2544023] using wordTrace_append hprefix tailTrace_2544023
  have hstable : (prefixWord ++ tailWord_2544023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544023).length < 2 ^ (prefixWord ++ tailWord_2544023).sum := by decide
  have hdescent : baseEnd_2544023 < baseStart_2544023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544030 : List Nat := [4, 3, 1, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2544030 : Nat := 118140960795 + 2544030 * 2 ^ 59
def prefixEnd_2544030 : Nat := 4983230072969 + 3 ^ 40 * 2544030 * 2
def baseEnd_2544030 : Nat := 435436729819262234875075

theorem tailTrace_2544030 : CollatzResearch.WordTrace tailWord_2544030 prefixEnd_2544030 435436729819262234875075 := by
  unfold tailWord_2544030
  simp only [CollatzResearch.WordTrace]
  refine ⟨11598549621677658822241693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61858931315614180385289029 11598549621677658822241693)
  ·
    refine ⟨4349456108129122058340635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11598549621677658822241693 4349456108129122058340635)
    ·
      refine ⟨6524184162193683087510953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4349456108129122058340635 6524184162193683087510953)
      ·
        refine ⟨4893138121645262315633215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6524184162193683087510953 4893138121645262315633215)
        ·
          refine ⟨7339707182467893473449823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893138121645262315633215 7339707182467893473449823)
          ·
            refine ⟨11009560773701840210174735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7339707182467893473449823 11009560773701840210174735)
            ·
              refine ⟨16514341160552760315262103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11009560773701840210174735 16514341160552760315262103)
              ·
                refine ⟨24771511740829140472893155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16514341160552760315262103 24771511740829140472893155)
                ·
                  refine ⟨37157267611243710709339733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24771511740829140472893155 37157267611243710709339733)
                  ·
                    refine ⟨435436729819262234875075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37157267611243710709339733 435436729819262234875075)
                    ·
                      rfl

theorem cell23_2544030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2544030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544030 prefixEnd_2544030 := by exact prefixLift 2544030
  have htrace : WordTrace (prefixWord ++ tailWord_2544030) baseStart_2544030 baseEnd_2544030 := by
    simpa [prefixWord, tailWord_2544030, baseEnd_2544030] using wordTrace_append hprefix tailTrace_2544030
  have hstable : (prefixWord ++ tailWord_2544030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544030).length < 2 ^ (prefixWord ++ tailWord_2544030).sum := by decide
  have hdescent : baseEnd_2544030 < baseStart_2544030 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544037 : List Nat := [1, 3, 1, 2, 1, 1, 3, 5, 2, 2, 2]
def baseStart_2544037 : Nat := 118140960795 + 2544037 * 2 ^ 59
def prefixEnd_2544037 : Nat := 4983230072969 + 3 ^ 40 * 2544037 * 2
def baseEnd_2544037 : Nat := 1306313783822368177237693

theorem tailTrace_2544037 : CollatzResearch.WordTrace tailWord_2544037 prefixEnd_2544037 1306313783822368177237693 := by
  unfold tailWord_2544037
  simp only [CollatzResearch.WordTrace]
  refine ⟨92788652284395910773438365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61859101522930607182292243 92788652284395910773438365)
  ·
    refine ⟨34795744606648466540039387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92788652284395910773438365 34795744606648466540039387)
    ·
      refine ⟨52193616909972699810059081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34795744606648466540039387 52193616909972699810059081)
      ·
        refine ⟨39145212682479524857544311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52193616909972699810059081 39145212682479524857544311)
        ·
          refine ⟨58717819023719287286316467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39145212682479524857544311 58717819023719287286316467)
          ·
            refine ⟨88076728535578930929474701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58717819023719287286316467 88076728535578930929474701)
            ·
              refine ⟨33028773200842099098553013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88076728535578930929474701 33028773200842099098553013)
              ·
                refine ⟨3096447487578946790489345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33028773200842099098553013 3096447487578946790489345)
                ·
                  refine ⟨2322335615684210092867009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3096447487578946790489345 2322335615684210092867009)
                  ·
                    refine ⟨1741751711763157569650257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2322335615684210092867009 1741751711763157569650257)
                    ·
                      refine ⟨1306313783822368177237693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1741751711763157569650257 1306313783822368177237693)
                      ·
                        rfl

theorem cell23_2544037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 3, 5, 2, 2, 2].length) (baseStart_2544037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544037 prefixEnd_2544037 := by exact prefixLift 2544037
  have htrace : WordTrace (prefixWord ++ tailWord_2544037) baseStart_2544037 baseEnd_2544037 := by
    simpa [prefixWord, tailWord_2544037, baseEnd_2544037] using wordTrace_append hprefix tailTrace_2544037
  have hstable : (prefixWord ++ tailWord_2544037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544037).length < 2 ^ (prefixWord ++ tailWord_2544037).sum := by decide
  have hdescent : baseEnd_2544037 < baseStart_2544037 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544065 : List Nat := [1, 2, 7, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_2544065 : Nat := 118140960795 + 2544065 * 2 ^ 59
def prefixEnd_2544065 : Nat := 4983230072969 + 3 ^ 40 * 2544065 * 2
def baseEnd_2544065 : Nat := 1306328161280694067687565

theorem tailTrace_2544065 : CollatzResearch.WordTrace tailWord_2544065 prefixEnd_2544065 1306328161280694067687565 := by
  unfold tailWord_2544065
  simp only [CollatzResearch.WordTrace]
  refine ⟨92789673528294471555457649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61859782352196314370305099 92789673528294471555457649)
  ·
    refine ⟨69592255146220853666593237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92789673528294471555457649 69592255146220853666593237)
    ·
      refine ⟨1631068479989551257810779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 69592255146220853666593237 1631068479989551257810779)
      ·
        refine ⟨2446602719984326886716169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1631068479989551257810779 2446602719984326886716169)
        ·
          refine ⟨1834952039988245165037127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2446602719984326886716169 1834952039988245165037127)
          ·
            refine ⟨2752428059982367747555691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834952039988245165037127 2752428059982367747555691)
            ·
              refine ⟨4128642089973551621333537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2752428059982367747555691 4128642089973551621333537)
              ·
                refine ⟨3096481567480163716000153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4128642089973551621333537 3096481567480163716000153)
                ·
                  refine ⟨2322361175610122787000115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3096481567480163716000153 2322361175610122787000115)
                  ·
                    refine ⟨3483541763415184180500173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2322361175610122787000115 3483541763415184180500173)
                    ·
                      refine ⟨1306328161280694067687565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3483541763415184180500173 1306328161280694067687565)
                      ·
                        rfl

theorem cell23_2544065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_2544065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544065 prefixEnd_2544065 := by exact prefixLift 2544065
  have htrace : WordTrace (prefixWord ++ tailWord_2544065) baseStart_2544065 baseEnd_2544065 := by
    simpa [prefixWord, tailWord_2544065, baseEnd_2544065] using wordTrace_append hprefix tailTrace_2544065
  have hstable : (prefixWord ++ tailWord_2544065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544065).length < 2 ^ (prefixWord ++ tailWord_2544065).sum := by decide
  have hdescent : baseEnd_2544065 < baseStart_2544065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544073 : List Nat := [1, 2, 1, 1, 2, 1, 4, 4, 2, 5]
def baseStart_2544073 : Nat := 118140960795 + 2544073 * 2 ^ 59
def prefixEnd_2544073 : Nat := 4983230072969 + 3 ^ 40 * 2544073 * 2
def baseEnd_2544073 : Nat := 435444089708643345462509

theorem tailTrace_2544073 : CollatzResearch.WordTrace tailWord_2544073 prefixEnd_2544073 435444089708643345462509 := by
  unfold tailWord_2544073
  simp only [CollatzResearch.WordTrace]
  refine ⟨92789965312265488921748873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61859976874843659281165915 92789965312265488921748873)
  ·
    refine ⟨69592473984199116691311655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92789965312265488921748873 69592473984199116691311655)
    ·
      refine ⟨104388710976298675036967483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69592473984199116691311655 104388710976298675036967483)
      ·
        refine ⟨156583066464448012555451225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104388710976298675036967483 156583066464448012555451225)
        ·
          refine ⟨117437299848336009416588419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156583066464448012555451225 117437299848336009416588419)
          ·
            refine ⟨176155949772504014124882629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117437299848336009416588419 176155949772504014124882629)
            ·
              refine ⟨33029240582344502648415493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176155949772504014124882629 33029240582344502648415493)
              ·
                refine ⟨6192982609189594246577905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33029240582344502648415493 6192982609189594246577905)
                ·
                  refine ⟨4644736956892195684933429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6192982609189594246577905 4644736956892195684933429)
                  ·
                    refine ⟨435444089708643345462509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4644736956892195684933429 435444089708643345462509)
                    ·
                      rfl

theorem cell23_2544073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_2544073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544073 prefixEnd_2544073 := by exact prefixLift 2544073
  have htrace : WordTrace (prefixWord ++ tailWord_2544073) baseStart_2544073 baseEnd_2544073 := by
    simpa [prefixWord, tailWord_2544073, baseEnd_2544073] using wordTrace_append hprefix tailTrace_2544073
  have hstable : (prefixWord ++ tailWord_2544073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544073).length < 2 ^ (prefixWord ++ tailWord_2544073).sum := by decide
  have hdescent : baseEnd_2544073 < baseStart_2544073 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544103 : List Nat := [1, 1, 5, 2, 1, 1, 1, 1, 2, 8]
def baseStart_2544103 : Nat := 118140960795 + 2544103 * 2 ^ 59
def prefixEnd_2544103 : Nat := 4983230072969 + 3 ^ 40 * 2544103 * 2
def baseEnd_2544103 : Nat := 435449224515188306337463

theorem tailTrace_2544103 : CollatzResearch.WordTrace tailWord_2544103 prefixEnd_2544103 435449224515188306337463 := by
  unfold tailWord_2544103
  simp only [CollatzResearch.WordTrace]
  refine ⟨92791059502156804045340963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61860706334771202696893975 92791059502156804045340963)
  ·
    refine ⟨139186589253235206068011445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92791059502156804045340963 139186589253235206068011445)
    ·
      refine ⟨13048742742490800568876073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139186589253235206068011445 13048742742490800568876073)
      ·
        refine ⟨9786557056868100426657055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13048742742490800568876073 9786557056868100426657055)
        ·
          refine ⟨14679835585302150639985583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9786557056868100426657055 14679835585302150639985583)
          ·
            refine ⟨22019753377953225959978375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14679835585302150639985583 22019753377953225959978375)
            ·
              refine ⟨33029630066929838939967563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22019753377953225959978375 33029630066929838939967563)
              ·
                refine ⟨49544445100394758409951345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33029630066929838939967563 49544445100394758409951345)
                ·
                  refine ⟨37158333825296068807463509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49544445100394758409951345 37158333825296068807463509)
                  ·
                    refine ⟨435449224515188306337463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 37158333825296068807463509 435449224515188306337463)
                    ·
                      rfl

theorem cell23_2544103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 8].length) (baseStart_2544103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544103 prefixEnd_2544103 := by exact prefixLift 2544103
  have htrace : WordTrace (prefixWord ++ tailWord_2544103) baseStart_2544103 baseEnd_2544103 := by
    simpa [prefixWord, tailWord_2544103, baseEnd_2544103] using wordTrace_append hprefix tailTrace_2544103
  have hstable : (prefixWord ++ tailWord_2544103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544103).length < 2 ^ (prefixWord ++ tailWord_2544103).sum := by decide
  have hdescent : baseEnd_2544103 < baseStart_2544103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544110 : List Nat := [4, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_2544110 : Nat := 118140960795 + 2544110 * 2 ^ 59
def prefixEnd_2544110 : Nat := 4983230072969 + 3 ^ 40 * 2544110 * 2
def baseEnd_2544110 : Nat := 1306351267910146391624857

theorem tailTrace_2544110 : CollatzResearch.WordTrace tailWord_2544110 prefixEnd_2544110 1306351267910146391624857 := by
  unfold tailWord_2544110
  simp only [CollatzResearch.WordTrace]
  refine ⟨11598914351641430530105723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61860876542087629493897189 11598914351641430530105723)
  ·
    refine ⟨17398371527462145795158585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11598914351641430530105723 17398371527462145795158585)
    ·
      refine ⟨13048778645596609346368939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17398371527462145795158585 13048778645596609346368939)
      ·
        refine ⟨19573167968394914019553409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13048778645596609346368939 19573167968394914019553409)
        ·
          refine ⟨14679875976296185514665057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19573167968394914019553409 14679875976296185514665057)
          ·
            refine ⟨11009906982222139135998793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14679875976296185514665057 11009906982222139135998793)
            ·
              refine ⟨8257430236666604351999095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11009906982222139135998793 8257430236666604351999095)
              ·
                refine ⟨12386145354999906527998643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8257430236666604351999095 12386145354999906527998643)
                ·
                  refine ⟨18579218032499859791997965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12386145354999906527998643 18579218032499859791997965)
                  ·
                    refine ⟨6967206762187447421999237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18579218032499859791997965 6967206762187447421999237)
                    ·
                      refine ⟨1306351267910146391624857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6967206762187447421999237 1306351267910146391624857)
                      ·
                        rfl

theorem cell23_2544110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_2544110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544110 prefixEnd_2544110 := by exact prefixLift 2544110
  have htrace : WordTrace (prefixWord ++ tailWord_2544110) baseStart_2544110 baseEnd_2544110 := by
    simpa [prefixWord, tailWord_2544110, baseEnd_2544110] using wordTrace_append hprefix tailTrace_2544110
  have hstable : (prefixWord ++ tailWord_2544110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544110).length < 2 ^ (prefixWord ++ tailWord_2544110).sum := by decide
  have hdescent : baseEnd_2544110 < baseStart_2544110 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544133 : List Nat := [1, 3, 1, 1, 2, 2, 4, 1, 8]
def baseStart_2544133 : Nat := 118140960795 + 2544133 * 2 ^ 59
def prefixEnd_2544133 : Nat := 4983230072969 + 3 ^ 40 * 2544133 * 2
def baseEnd_2544133 : Nat := 145151453107244422404139

theorem tailTrace_2544133 : CollatzResearch.WordTrace tailWord_2544133 prefixEnd_2544133 145151453107244422404139 := by
  unfold tailWord_2544133
  simp only [CollatzResearch.WordTrace]
  refine ⟨92792153692048119168933053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61861435794698746112622035 92792153692048119168933053)
  ·
    refine ⟨34797057634518044688349895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92792153692048119168933053 34797057634518044688349895)
    ·
      refine ⟨52195586451777067032524843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34797057634518044688349895 52195586451777067032524843)
      ·
        refine ⟨78293379677665600548787265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52195586451777067032524843 78293379677665600548787265)
        ·
          refine ⟨58720034758249200411590449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78293379677665600548787265 58720034758249200411590449)
          ·
            refine ⟨44040026068686900308692837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58720034758249200411590449 44040026068686900308692837)
            ·
              refine ⟨8257504887878793807879907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44040026068686900308692837 8257504887878793807879907)
              ·
                refine ⟨12386257331818190711819861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8257504887878793807879907 12386257331818190711819861)
                ·
                  refine ⟨145151453107244422404139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12386257331818190711819861 145151453107244422404139)
                  ·
                    rfl

theorem cell23_2544133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_2544133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544133 prefixEnd_2544133 := by exact prefixLift 2544133
  have htrace : WordTrace (prefixWord ++ tailWord_2544133) baseStart_2544133 baseEnd_2544133 := by
    simpa [prefixWord, tailWord_2544133, baseEnd_2544133] using wordTrace_append hprefix tailTrace_2544133
  have hstable : (prefixWord ++ tailWord_2544133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544133).length < 2 ^ (prefixWord ++ tailWord_2544133).sum := by decide
  have hdescent : baseEnd_2544133 < baseStart_2544133 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544134 : List Nat := [6, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7]
def baseStart_2544134 : Nat := 118140960795 + 2544134 * 2 ^ 59
def prefixEnd_2544134 : Nat := 4983230072969 + 3 ^ 40 * 2544134 * 2
def baseEnd_2544134 : Nat := 1306363591445854297724747

theorem tailTrace_2544134 : CollatzResearch.WordTrace tailWord_2544134 prefixEnd_2544134 1306363591445854297724747 := by
  unfold tailWord_2544134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2899755942657640510616233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61861460110029664226479637 2899755942657640510616233)
  ·
    refine ⟨2174816956993230382962175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2899755942657640510616233 2174816956993230382962175)
    ·
      refine ⟨3262225435489845574443263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2174816956993230382962175 3262225435489845574443263)
      ·
        refine ⟨4893338153234768361664895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262225435489845574443263 4893338153234768361664895)
        ·
          refine ⟨7340007229852152542497343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893338153234768361664895 7340007229852152542497343)
          ·
            refine ⟨11010010844778228813746015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7340007229852152542497343 11010010844778228813746015)
            ·
              refine ⟨16515016267167343220619023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11010010844778228813746015 16515016267167343220619023)
              ·
                refine ⟨24772524400751014830928535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16515016267167343220619023 24772524400751014830928535)
                ·
                  refine ⟨37158786601126522246392803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24772524400751014830928535 37158786601126522246392803)
                  ·
                    refine ⟨55738179901689783369589205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37158786601126522246392803 55738179901689783369589205)
                    ·
                      refine ⟨1306363591445854297724747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55738179901689783369589205 1306363591445854297724747)
                      ·
                        rfl

theorem cell23_2544134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_2544134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544134 prefixEnd_2544134 := by exact prefixLift 2544134
  have htrace : WordTrace (prefixWord ++ tailWord_2544134) baseStart_2544134 baseEnd_2544134 := by
    simpa [prefixWord, tailWord_2544134, baseEnd_2544134] using wordTrace_append hprefix tailTrace_2544134
  have hstable : (prefixWord ++ tailWord_2544134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544134).length < 2 ^ (prefixWord ++ tailWord_2544134).sum := by decide
  have hdescent : baseEnd_2544134 < baseStart_2544134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544223 : List Nat := [1, 1, 2, 3, 1, 1, 1, 13]
def baseStart_2544223 : Nat := 118140960795 + 2544223 * 2 ^ 59
def prefixEnd_2544223 : Nat := 4983230072969 + 3 ^ 40 * 2544223 * 2
def baseEnd_2544223 : Nat := 48385529304596461093031

theorem tailTrace_2544223 : CollatzResearch.WordTrace tailWord_2544223 prefixEnd_2544223 48385529304596461093031 := by
  unfold tailWord_2544223
  simp only [CollatzResearch.WordTrace]
  refine ⟨92795436261722064539709323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61863624174481376359806215 92795436261722064539709323)
  ·
    refine ⟨139193154392583096809563985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92795436261722064539709323 139193154392583096809563985)
    ·
      refine ⟨104394865794437322607172989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139193154392583096809563985 104394865794437322607172989)
      ·
        refine ⟨39148074672913995977689871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104394865794437322607172989 39148074672913995977689871)
        ·
          refine ⟨58722112009370993966534807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39148074672913995977689871 58722112009370993966534807)
          ·
            refine ⟨88083168014056490949802211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58722112009370993966534807 88083168014056490949802211)
            ·
              refine ⟨132124752021084736424703317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88083168014056490949802211 132124752021084736424703317)
              ·
                refine ⟨48385529304596461093031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 132124752021084736424703317 48385529304596461093031)
                ·
                  rfl

theorem cell23_2544223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 13].length) (baseStart_2544223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544223 prefixEnd_2544223 := by exact prefixLift 2544223
  have htrace : WordTrace (prefixWord ++ tailWord_2544223) baseStart_2544223 baseEnd_2544223 := by
    simpa [prefixWord, tailWord_2544223, baseEnd_2544223] using wordTrace_append hprefix tailTrace_2544223
  have hstable : (prefixWord ++ tailWord_2544223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544223).length < 2 ^ (prefixWord ++ tailWord_2544223).sum := by decide
  have hdescent : baseEnd_2544223 < baseStart_2544223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544234 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2]
def baseStart_2544234 : Nat := 118140960795 + 2544234 * 2 ^ 59
def prefixEnd_2544234 : Nat := 4983230072969 + 3 ^ 40 * 2544234 * 2
def baseEnd_2544234 : Nat := 1306414939511303906474287

theorem tailTrace_2544234 : CollatzResearch.WordTrace tailWord_2544234 prefixEnd_2544234 1306414939511303906474287 := by
  unfold tailWord_2544234
  simp only [CollatzResearch.WordTrace]
  refine ⟨23198959366170553354589939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61863891643121475612239837 23198959366170553354589939)
  ·
    refine ⟨34798439049255830031884909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23198959366170553354589939 34798439049255830031884909)
    ·
      refine ⟨13049414643470936261956841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34798439049255830031884909 13049414643470936261956841)
      ·
        refine ⟨9787060982603202196467631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13049414643470936261956841 9787060982603202196467631)
        ·
          refine ⟨14680591473904803294701447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9787060982603202196467631 14680591473904803294701447)
          ·
            refine ⟨22020887210857204942052171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14680591473904803294701447 22020887210857204942052171)
            ·
              refine ⟨33031330816285807413078257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22020887210857204942052171 33031330816285807413078257)
              ·
                refine ⟨24773498112214355559808693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33031330816285807413078257 24773498112214355559808693)
                ·
                  refine ⟨2322515448020095833732065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24773498112214355559808693 2322515448020095833732065)
                  ·
                    refine ⟨1741886586015071875299049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2322515448020095833732065 1741886586015071875299049)
                    ·
                      refine ⟨1306414939511303906474287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1741886586015071875299049 1306414939511303906474287)
                      ·
                        rfl

theorem cell23_2544234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_2544234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544234 prefixEnd_2544234 := by exact prefixLift 2544234
  have htrace : WordTrace (prefixWord ++ tailWord_2544234) baseStart_2544234 baseEnd_2544234 := by
    simpa [prefixWord, tailWord_2544234, baseEnd_2544234] using wordTrace_append hprefix tailTrace_2544234
  have hstable : (prefixWord ++ tailWord_2544234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544234).length < 2 ^ (prefixWord ++ tailWord_2544234).sum := by decide
  have hdescent : baseEnd_2544234 < baseStart_2544234 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544240 : List Nat := [2, 1, 1, 1, 7, 1, 10]
def baseStart_2544240 : Nat := 118140960795 + 2544240 * 2 ^ 59
def prefixEnd_2544240 : Nat := 4983230072969 + 3 ^ 40 * 2544240 * 2
def baseEnd_2544240 : Nat := 16128617535743591148139

theorem tailTrace_2544240 : CollatzResearch.WordTrace tailWord_2544240 prefixEnd_2544240 16128617535743591148139 := by
  unfold tailWord_2544240
  simp only [CollatzResearch.WordTrace]
  refine ⟨46398028151330238221539087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61864037535106984295385449 46398028151330238221539087)
  ·
    refine ⟨69597042226995357332308631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46398028151330238221539087 69597042226995357332308631)
    ·
      refine ⟨104395563340493035998462947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69597042226995357332308631 104395563340493035998462947)
      ·
        refine ⟨156593345010739553997694421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104395563340493035998462947 156593345010739553997694421)
        ·
          refine ⟨3670156523689208296820963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 156593345010739553997694421 3670156523689208296820963)
          ·
            refine ⟨5505234785533812445231445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3670156523689208296820963 5505234785533812445231445)
            ·
              refine ⟨16128617535743591148139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 5505234785533812445231445 16128617535743591148139)
              ·
                rfl

theorem cell23_2544240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 1, 10].length) (baseStart_2544240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544240 prefixEnd_2544240 := by exact prefixLift 2544240
  have htrace : WordTrace (prefixWord ++ tailWord_2544240) baseStart_2544240 baseEnd_2544240 := by
    simpa [prefixWord, tailWord_2544240, baseEnd_2544240] using wordTrace_append hprefix tailTrace_2544240
  have hstable : (prefixWord ++ tailWord_2544240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544240).length < 2 ^ (prefixWord ++ tailWord_2544240).sum := by decide
  have hdescent : baseEnd_2544240 < baseStart_2544240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544274 : List Nat := [3, 2, 3, 1, 2, 3, 2, 7]
def baseStart_2544274 : Nat := 118140960795 + 2544274 * 2 ^ 59
def prefixEnd_2544274 : Nat := 4983230072969 + 3 ^ 40 * 2544274 * 2
def baseEnd_2544274 : Nat := 48386499212499398147189

theorem tailTrace_2544274 : CollatzResearch.WordTrace tailWord_2544274 prefixEnd_2544274 48386499212499398147189 := by
  unfold tailWord_2544274
  simp only [CollatzResearch.WordTrace]
  refine ⟨23199324096134325062453969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61864864256358200166543917 23199324096134325062453969)
  ·
    refine ⟨17399493072100743796840477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23199324096134325062453969 17399493072100743796840477)
    ·
      refine ⟨6524809902037778923815179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17399493072100743796840477 6524809902037778923815179)
      ·
        refine ⟨9787214853056668385722769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6524809902037778923815179 9787214853056668385722769)
        ·
          refine ⟨7340411139792501289292077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9787214853056668385722769 7340411139792501289292077)
          ·
            refine ⟨2752654177422187983484529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7340411139792501289292077 2752654177422187983484529)
            ·
              refine ⟨2064490633066640987613397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2752654177422187983484529 2064490633066640987613397)
              ·
                refine ⟨48386499212499398147189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2064490633066640987613397 48386499212499398147189)
                ·
                  rfl

theorem cell23_2544274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 3, 2, 7].length) (baseStart_2544274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544274 prefixEnd_2544274 := by exact prefixLift 2544274
  have htrace : WordTrace (prefixWord ++ tailWord_2544274) baseStart_2544274 baseEnd_2544274 := by
    simpa [prefixWord, tailWord_2544274, baseEnd_2544274] using wordTrace_append hprefix tailTrace_2544274
  have hstable : (prefixWord ++ tailWord_2544274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544274).length < 2 ^ (prefixWord ++ tailWord_2544274).sum := by decide
  have hdescent : baseEnd_2544274 < baseStart_2544274 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544280 : List Nat := [2, 1, 2, 4, 1, 1, 1, 1, 1, 4, 5]
def baseStart_2544280 : Nat := 118140960795 + 2544280 * 2 ^ 59
def prefixEnd_2544280 : Nat := 4983230072969 + 3 ^ 40 * 2544280 * 2
def baseEnd_2544280 : Nat := 1306438559621410726499075

theorem tailTrace_2544280 : CollatzResearch.WordTrace tailWord_2544280 prefixEnd_2544280 1306438559621410726499075 := by
  unfold tailWord_2544280
  simp only [CollatzResearch.WordTrace]
  refine ⟨46398757611257781637267147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61865010148343708849689529 46398757611257781637267147)
  ·
    refine ⟨69598136416886672455900721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46398757611257781637267147 69598136416886672455900721)
    ·
      refine ⟨52198602312665004341925541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69598136416886672455900721 52198602312665004341925541)
      ·
        refine ⟨9787237933624688314111039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52198602312665004341925541 9787237933624688314111039)
        ·
          refine ⟨14680856900437032471166559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9787237933624688314111039 14680856900437032471166559)
          ·
            refine ⟨22021285350655548706749839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14680856900437032471166559 22021285350655548706749839)
            ·
              refine ⟨33031928025983323060124759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22021285350655548706749839 33031928025983323060124759)
              ·
                refine ⟨49547892038974984590187139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33031928025983323060124759 49547892038974984590187139)
                ·
                  refine ⟨74321838058462476885280709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49547892038974984590187139 74321838058462476885280709)
                  ·
                    refine ⟨13935344635961714415990133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74321838058462476885280709 13935344635961714415990133)
                    ·
                      refine ⟨1306438559621410726499075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13935344635961714415990133 1306438559621410726499075)
                      ·
                        rfl

theorem cell23_2544280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_2544280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544280 prefixEnd_2544280 := by exact prefixLift 2544280
  have htrace : WordTrace (prefixWord ++ tailWord_2544280) baseStart_2544280 baseEnd_2544280 := by
    simpa [prefixWord, tailWord_2544280, baseEnd_2544280] using wordTrace_append hprefix tailTrace_2544280
  have hstable : (prefixWord ++ tailWord_2544280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544280).length < 2 ^ (prefixWord ++ tailWord_2544280).sum := by decide
  have hdescent : baseEnd_2544280 < baseStart_2544280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544284 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 4, 1, 3]
def baseStart_2544284 : Nat := 118140960795 + 2544284 * 2 ^ 59
def prefixEnd_2544284 : Nat := 4983230072969 + 3 ^ 40 * 2544284 * 2
def baseEnd_2544284 : Nat := 1306440613544028710849057

theorem tailTrace_2544284 : CollatzResearch.WordTrace tailWord_2544284 prefixEnd_2544284 1306440613544028710849057 := by
  unfold tailWord_2544284
  simp only [CollatzResearch.WordTrace]
  refine ⟨46398830557250535978839953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61865107409667381305119937 46398830557250535978839953)
  ·
    refine ⟨34799122917937901984129965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46398830557250535978839953 34799122917937901984129965)
    ·
      refine ⟨13049671094226713244048737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34799122917937901984129965 13049671094226713244048737)
      ·
        refine ⟨9787253320670034933036553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13049671094226713244048737 9787253320670034933036553)
        ·
          refine ⟨7340439990502526199777415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9787253320670034933036553 7340439990502526199777415)
          ·
            refine ⟨11010659985753789299666123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7340439990502526199777415 11010659985753789299666123)
            ·
              refine ⟨16515989978630683949499185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11010659985753789299666123 16515989978630683949499185)
              ·
                refine ⟨12386992483973012962124389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16515989978630683949499185 12386992483973012962124389)
                ·
                  refine ⟨2322561090744939930398323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12386992483973012962124389 2322561090744939930398323)
                  ·
                    refine ⟨3483841636117409895597485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2322561090744939930398323 3483841636117409895597485)
                    ·
                      refine ⟨1306440613544028710849057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3483841636117409895597485 1306440613544028710849057)
                      ·
                        rfl

theorem cell23_2544284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_2544284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544284 prefixEnd_2544284 := by exact prefixLift 2544284
  have htrace : WordTrace (prefixWord ++ tailWord_2544284) baseStart_2544284 baseEnd_2544284 := by
    simpa [prefixWord, tailWord_2544284, baseEnd_2544284] using wordTrace_append hprefix tailTrace_2544284
  have hstable : (prefixWord ++ tailWord_2544284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544284).length < 2 ^ (prefixWord ++ tailWord_2544284).sum := by decide
  have hdescent : baseEnd_2544284 < baseStart_2544284 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544302 : List Nat := [4, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_2544302 : Nat := 118140960795 + 2544302 * 2 ^ 59
def prefixEnd_2544302 : Nat := 4983230072969 + 3 ^ 40 * 2544302 * 2
def baseEnd_2544302 : Nat := 1306449856195809640423975

theorem tailTrace_2544302 : CollatzResearch.WordTrace tailWord_2544302 prefixEnd_2544302 1306449856195809640423975 := by
  unfold tailWord_2544302
  simp only [CollatzResearch.WordTrace]
  refine ⟨11599789703554482628979395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61865545085623907354556773 11599789703554482628979395)
  ·
    refine ⟨17399684555331723943469093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11599789703554482628979395 17399684555331723943469093)
    ·
      refine ⟨3262440854124698239400455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17399684555331723943469093 3262440854124698239400455)
      ·
        refine ⟨4893661281187047359100683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3262440854124698239400455 4893661281187047359100683)
        ·
          refine ⟨7340491921780571038651025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4893661281187047359100683 7340491921780571038651025)
          ·
            refine ⟨5505368941335428278988269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7340491921780571038651025 5505368941335428278988269)
            ·
              refine ⟨2064513353000785604620601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5505368941335428278988269 2064513353000785604620601)
              ·
                refine ⟨1548385014750589203465451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2064513353000785604620601 1548385014750589203465451)
                ·
                  refine ⟨2322577522125883805198177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548385014750589203465451 2322577522125883805198177)
                  ·
                    refine ⟨1741933141594412853898633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2322577522125883805198177 1741933141594412853898633)
                    ·
                      refine ⟨1306449856195809640423975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1741933141594412853898633 1306449856195809640423975)
                      ·
                        rfl

theorem cell23_2544302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_2544302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544302 prefixEnd_2544302 := by exact prefixLift 2544302
  have htrace : WordTrace (prefixWord ++ tailWord_2544302) baseStart_2544302 baseEnd_2544302 := by
    simpa [prefixWord, tailWord_2544302, baseEnd_2544302] using wordTrace_append hprefix tailTrace_2544302
  have hstable : (prefixWord ++ tailWord_2544302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544302).length < 2 ^ (prefixWord ++ tailWord_2544302).sum := by decide
  have hdescent : baseEnd_2544302 < baseStart_2544302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544374 : List Nat := [5, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3]
def baseStart_2544374 : Nat := 118140960795 + 2544374 * 2 ^ 59
def prefixEnd_2544374 : Nat := 4983230072969 + 3 ^ 40 * 2544374 * 2
def baseEnd_2544374 : Nat := 1306486826802933358723643

theorem tailTrace_2544374 : CollatzResearch.WordTrace tailWord_2544374 prefixEnd_2544374 1306486826802933358723643 := by
  unfold tailWord_2544374
  simp only [CollatzResearch.WordTrace]
  refine ⟨5800058980260938583028511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61867295789450011552304117 5800058980260938583028511)
  ·
    refine ⟨8700088470391407874542767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5800058980260938583028511 8700088470391407874542767)
    ·
      refine ⟨13050132705587111811814151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8700088470391407874542767 13050132705587111811814151)
      ·
        refine ⟨19575199058380667717721227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13050132705587111811814151 19575199058380667717721227)
        ·
          refine ⟨29362798587571001576581841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19575199058380667717721227 29362798587571001576581841)
          ·
            refine ⟨22022098940678251182436381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29362798587571001576581841 22022098940678251182436381)
            ·
              refine ⟨8258287102754344193413643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22022098940678251182436381 8258287102754344193413643)
              ·
                refine ⟨12387430654131516290120465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8258287102754344193413643 12387430654131516290120465)
                ·
                  refine ⟨9290572990598637217590349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12387430654131516290120465 9290572990598637217590349)
                  ·
                    refine ⟨3483964871474488956596381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9290572990598637217590349 3483964871474488956596381)
                    ·
                      refine ⟨1306486826802933358723643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3483964871474488956596381 1306486826802933358723643)
                      ·
                        rfl

theorem cell23_2544374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 3, 1, 2, 3, 3].length) (baseStart_2544374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544374 prefixEnd_2544374 := by exact prefixLift 2544374
  have htrace : WordTrace (prefixWord ++ tailWord_2544374) baseStart_2544374 baseEnd_2544374 := by
    simpa [prefixWord, tailWord_2544374, baseEnd_2544374] using wordTrace_append hprefix tailTrace_2544374
  have hstable : (prefixWord ++ tailWord_2544374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544374).length < 2 ^ (prefixWord ++ tailWord_2544374).sum := by decide
  have hdescent : baseEnd_2544374 < baseStart_2544374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544464 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 5, 1, 3]
def baseStart_2544464 : Nat := 118140960795 + 2544464 * 2 ^ 59
def prefixEnd_2544464 : Nat := 4983230072969 + 3 ^ 40 * 2544464 * 2
def baseEnd_2544464 : Nat := 1306533040061838006598229

theorem tailTrace_2544464 : CollatzResearch.WordTrace tailWord_2544464 prefixEnd_2544464 1306533040061838006598229 := by
  unfold tailWord_2544464
  simp only [CollatzResearch.WordTrace]
  refine ⟨46402113126924481349616223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61869484169232641799488297 46402113126924481349616223)
  ·
    refine ⟨69603169690386722024424335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46402113126924481349616223 69603169690386722024424335)
    ·
      refine ⟨104404754535580083036636503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69603169690386722024424335 104404754535580083036636503)
      ·
        refine ⟨156607131803370124554954755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104404754535580083036636503 156607131803370124554954755)
        ·
          refine ⟨234910697705055186832432133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156607131803370124554954755 234910697705055186832432133)
          ·
            refine ⟨44045755819697847531081025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 234910697705055186832432133 44045755819697847531081025)
            ·
              refine ⟨33034316864773385648310769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44045755819697847531081025 33034316864773385648310769)
              ·
                refine ⟨24775737648580039236233077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33034316864773385648310769 24775737648580039236233077)
                ·
                  refine ⟨2322725404554378678396851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 24775737648580039236233077 2322725404554378678396851)
                  ·
                    refine ⟨3484088106831568017595277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2322725404554378678396851 3484088106831568017595277)
                    ·
                      refine ⟨1306533040061838006598229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3484088106831568017595277 1306533040061838006598229)
                      ·
                        rfl

theorem cell23_2544464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 5, 1, 3].length) (baseStart_2544464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544464 prefixEnd_2544464 := by exact prefixLift 2544464
  have htrace : WordTrace (prefixWord ++ tailWord_2544464) baseStart_2544464 baseEnd_2544464 := by
    simpa [prefixWord, tailWord_2544464, baseEnd_2544464] using wordTrace_append hprefix tailTrace_2544464
  have hstable : (prefixWord ++ tailWord_2544464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544464).length < 2 ^ (prefixWord ++ tailWord_2544464).sum := by decide
  have hdescent : baseEnd_2544464 < baseStart_2544464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544501 : List Nat := [1, 3, 4, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2544501 : Nat := 118140960795 + 2544501 * 2 ^ 59
def prefixEnd_2544501 : Nat := 4983230072969 + 3 ^ 40 * 2544501 * 2
def baseEnd_2544501 : Nat := 435517346282018120611853

theorem tailTrace_2544501 : CollatzResearch.WordTrace tailWord_2544501 prefixEnd_2544501 435517346282018120611853 := by
  unfold tailWord_2544501
  simp only [CollatzResearch.WordTrace]
  refine ⟨92805575754714918018329357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61870383836476612012219571 92805575754714918018329357)
  ·
    refine ⟨34802090908018094256873509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92805575754714918018329357 34802090908018094256873509)
    ·
      refine ⟨6525392045253392673163783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34802090908018094256873509 6525392045253392673163783)
      ·
        refine ⟨9788088067880089009745675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6525392045253392673163783 9788088067880089009745675)
        ·
          refine ⟨14682132101820133514618513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9788088067880089009745675 14682132101820133514618513)
          ·
            refine ⟨11011599076365100135963885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14682132101820133514618513 11011599076365100135963885)
            ·
              refine ⟨4129349653636912550986457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11011599076365100135963885 4129349653636912550986457)
              ·
                refine ⟨3097012240227684413239843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4129349653636912550986457 3097012240227684413239843)
                ·
                  refine ⟨4645518360341526619859765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097012240227684413239843 4645518360341526619859765)
                  ·
                    refine ⟨435517346282018120611853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4645518360341526619859765 435517346282018120611853)
                    ·
                      rfl

theorem cell23_2544501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2544501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544501 prefixEnd_2544501 := by exact prefixLift 2544501
  have htrace : WordTrace (prefixWord ++ tailWord_2544501) baseStart_2544501 baseEnd_2544501 := by
    simpa [prefixWord, tailWord_2544501, baseEnd_2544501] using wordTrace_append hprefix tailTrace_2544501
  have hstable : (prefixWord ++ tailWord_2544501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544501).length < 2 ^ (prefixWord ++ tailWord_2544501).sum := by decide
  have hdescent : baseEnd_2544501 < baseStart_2544501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544504 : List Nat := [2, 1, 2, 1, 1, 1, 1, 8, 1, 1, 4]
def baseStart_2544504 : Nat := 118140960795 + 2544504 * 2 ^ 59
def prefixEnd_2544504 : Nat := 4983230072969 + 3 ^ 40 * 2544504 * 2
def baseEnd_2544504 : Nat := 1306553579288017850098045

theorem tailTrace_2544504 : CollatzResearch.WordTrace tailWord_2544504 prefixEnd_2544504 1306553579288017850098045 := by
  unfold tailWord_2544504
  simp only [CollatzResearch.WordTrace]
  refine ⟨46402842586852024765344283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61870456782469366353792377 46402842586852024765344283)
  ·
    refine ⟨69604263880278037148016425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46402842586852024765344283 69604263880278037148016425)
    ·
      refine ⟨52203197910208527861012319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69604263880278037148016425 52203197910208527861012319)
      ·
        refine ⟨78304796865312791791518479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52203197910208527861012319 78304796865312791791518479)
        ·
          refine ⟨117457195297969187687277719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78304796865312791791518479 117457195297969187687277719)
          ·
            refine ⟨176185792946953781530916579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117457195297969187687277719 176185792946953781530916579)
            ·
              refine ⟨264278689420430672296374869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176185792946953781530916579 264278689420430672296374869)
              ·
                refine ⟨3097015891645671940973143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 264278689420430672296374869 3097015891645671940973143)
                ·
                  refine ⟨4645523837468507911459715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097015891645671940973143 4645523837468507911459715)
                  ·
                    refine ⟨6968285756202761867189573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4645523837468507911459715 6968285756202761867189573)
                    ·
                      refine ⟨1306553579288017850098045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6968285756202761867189573 1306553579288017850098045)
                      ·
                        rfl

theorem cell23_2544504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 8, 1, 1, 4].length) (baseStart_2544504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544504 prefixEnd_2544504 := by exact prefixLift 2544504
  have htrace : WordTrace (prefixWord ++ tailWord_2544504) baseStart_2544504 baseEnd_2544504 := by
    simpa [prefixWord, tailWord_2544504, baseEnd_2544504] using wordTrace_append hprefix tailTrace_2544504
  have hstable : (prefixWord ++ tailWord_2544504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544504).length < 2 ^ (prefixWord ++ tailWord_2544504).sum := by decide
  have hdescent : baseEnd_2544504 < baseStart_2544504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544507 : List Nat := [1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 5]
def baseStart_2544507 : Nat := 118140960795 + 2544507 * 2 ^ 59
def prefixEnd_2544507 : Nat := 4983230072969 + 3 ^ 40 * 2544507 * 2
def baseEnd_2544507 : Nat := 1306555119729981338360531

theorem tailTrace_2544507 : CollatzResearch.WordTrace tailWord_2544507 prefixEnd_2544507 1306555119729981338360531 := by
  unfold tailWord_2544507
  simp only [CollatzResearch.WordTrace]
  refine ⟨92805794592693181043047775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61870529728462120695365183 92805794592693181043047775)
  ·
    refine ⟨139208691889039771564571663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92805794592693181043047775 139208691889039771564571663)
    ·
      refine ⟨208813037833559657346857495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139208691889039771564571663 208813037833559657346857495)
      ·
        refine ⟨313219556750339486020286243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208813037833559657346857495 313219556750339486020286243)
        ·
          refine ⟨469829335125509229030429365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313219556750339486020286243 469829335125509229030429365)
          ·
            refine ⟨44046500168016490221602753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 469829335125509229030429365 44046500168016490221602753)
            ·
              refine ⟨33034875126012367666202065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44046500168016490221602753 33034875126012367666202065)
              ·
                refine ⟨24776156344509275749651549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33034875126012367666202065 24776156344509275749651549)
                ·
                  refine ⟨9291058629190978406119331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24776156344509275749651549 9291058629190978406119331)
                  ·
                    refine ⟨13936587943786467609178997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9291058629190978406119331 13936587943786467609178997)
                    ·
                      refine ⟨1306555119729981338360531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13936587943786467609178997 1306555119729981338360531)
                      ·
                        rfl

theorem cell23_2544507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 3, 1, 5].length) (baseStart_2544507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544507 prefixEnd_2544507 := by exact prefixLift 2544507
  have htrace : WordTrace (prefixWord ++ tailWord_2544507) baseStart_2544507 baseEnd_2544507 := by
    simpa [prefixWord, tailWord_2544507, baseEnd_2544507] using wordTrace_append hprefix tailTrace_2544507
  have hstable : (prefixWord ++ tailWord_2544507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544507).length < 2 ^ (prefixWord ++ tailWord_2544507).sum := by decide
  have hdescent : baseEnd_2544507 < baseStart_2544507 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544524 : List Nat := [2, 2, 1, 2, 1, 2, 5, 1, 1, 1, 5]
def baseStart_2544524 : Nat := 118140960795 + 2544524 * 2 ^ 59
def prefixEnd_2544524 : Nat := 4983230072969 + 3 ^ 40 * 2544524 * 2
def baseEnd_2544524 : Nat := 1306563848901107771847953

theorem tailTrace_2544524 : CollatzResearch.WordTrace tailWord_2544524 prefixEnd_2544524 1306563848901107771847953 := by
  unfold tailWord_2544524
  simp only [CollatzResearch.WordTrace]
  refine ⟨46403207316815796473208313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61870943089087728630944417 46403207316815796473208313)
  ·
    refine ⟨34802405487611847354906235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46403207316815796473208313 34802405487611847354906235)
    ·
      refine ⟨52203608231417771032359353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34802405487611847354906235 52203608231417771032359353)
      ·
        refine ⟨39152706173563328274269515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52203608231417771032359353 39152706173563328274269515)
        ·
          refine ⟨58729059260344992411404273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39152706173563328274269515 58729059260344992411404273)
          ·
            refine ⟨44046794445258744308553205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58729059260344992411404273 44046794445258744308553205)
            ·
              refine ⟨4129386979243007278926863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 44046794445258744308553205 4129386979243007278926863)
              ·
                refine ⟨6194080468864510918390295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4129386979243007278926863 6194080468864510918390295)
                ·
                  refine ⟨9291120703296766377585443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194080468864510918390295 9291120703296766377585443)
                  ·
                    refine ⟨13936681054945149566378165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9291120703296766377585443 13936681054945149566378165)
                    ·
                      refine ⟨1306563848901107771847953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13936681054945149566378165 1306563848901107771847953)
                      ·
                        rfl

theorem cell23_2544524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_2544524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544524 prefixEnd_2544524 := by exact prefixLift 2544524
  have htrace : WordTrace (prefixWord ++ tailWord_2544524) baseStart_2544524 baseEnd_2544524 := by
    simpa [prefixWord, tailWord_2544524, baseEnd_2544524] using wordTrace_append hprefix tailTrace_2544524
  have hstable : (prefixWord ++ tailWord_2544524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544524).length < 2 ^ (prefixWord ++ tailWord_2544524).sum := by decide
  have hdescent : baseEnd_2544524 < baseStart_2544524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544547 : List Nat := [1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 6]
def baseStart_2544547 : Nat := 118140960795 + 2544547 * 2 ^ 59
def prefixEnd_2544547 : Nat := 4983230072969 + 3 ^ 40 * 2544547 * 2
def baseEnd_2544547 : Nat := 1306575658956161181860347

theorem tailTrace_2544547 : CollatzResearch.WordTrace tailWord_2544547 prefixEnd_2544547 1306575658956161181860347 := by
  unfold tailWord_2544547
  simp only [CollatzResearch.WordTrace]
  refine ⟨92807253512548267874503895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61871502341698845249669263 92807253512548267874503895)
  ·
    refine ⟨139210880268822401811755843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92807253512548267874503895 139210880268822401811755843)
    ·
      refine ⟨208816320403233602717633765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139210880268822401811755843 208816320403233602717633765)
      ·
        refine ⟨39153060075606300509556331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208816320403233602717633765 39153060075606300509556331)
        ·
          refine ⟨58729590113409450764334497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39153060075606300509556331 58729590113409450764334497)
          ·
            refine ⟨44047192585057088073250873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58729590113409450764334497 44047192585057088073250873)
            ·
              refine ⟨33035394438792816054938155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44047192585057088073250873 33035394438792816054938155)
              ·
                refine ⟨49553091658189224082407233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33035394438792816054938155 49553091658189224082407233)
                ·
                  refine ⟨37164818743641918061805425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49553091658189224082407233 37164818743641918061805425)
                  ·
                    refine ⟨27873614057731438546354069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 37164818743641918061805425 27873614057731438546354069)
                    ·
                      refine ⟨1306575658956161181860347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27873614057731438546354069 1306575658956161181860347)
                      ·
                        rfl

theorem cell23_2544547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_2544547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544547 prefixEnd_2544547 := by exact prefixLift 2544547
  have htrace : WordTrace (prefixWord ++ tailWord_2544547) baseStart_2544547 baseEnd_2544547 := by
    simpa [prefixWord, tailWord_2544547, baseEnd_2544547] using wordTrace_append hprefix tailTrace_2544547
  have hstable : (prefixWord ++ tailWord_2544547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544547).length < 2 ^ (prefixWord ++ tailWord_2544547).sum := by decide
  have hdescent : baseEnd_2544547 < baseStart_2544547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544561 : List Nat := [1, 2, 2, 4, 3, 1, 3, 7]
def baseStart_2544561 : Nat := 118140960795 + 2544561 * 2 ^ 59
def prefixEnd_2544561 : Nat := 4983230072969 + 3 ^ 40 * 2544561 * 2
def baseEnd_2544561 : Nat := 48391957321678671373529

theorem tailTrace_2544561 : CollatzResearch.WordTrace tailWord_2544561 prefixEnd_2544561 48391957321678671373529 := by
  unfold tailWord_2544561
  simp only [CollatzResearch.WordTrace]
  refine ⟨92807764134497548265513537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61871842756331698843675691 92807764134497548265513537)
  ·
    refine ⟨69605823100873161199135153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92807764134497548265513537 69605823100873161199135153)
    ·
      refine ⟨52204367325654870899351365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69605823100873161199135153 52204367325654870899351365)
      ·
        refine ⟨9788318873560288293628381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52204367325654870899351365 9788318873560288293628381)
        ·
          refine ⟨3670619577585108110110643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9788318873560288293628381 3670619577585108110110643)
          ·
            refine ⟨5505929366377662165165965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3670619577585108110110643 5505929366377662165165965)
            ·
              refine ⟨2064723512391623311937237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5505929366377662165165965 2064723512391623311937237)
              ·
                refine ⟨48391957321678671373529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2064723512391623311937237 48391957321678671373529)
                ·
                  rfl

theorem cell23_2544561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 3, 7].length) (baseStart_2544561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544561 prefixEnd_2544561 := by exact prefixLift 2544561
  have htrace : WordTrace (prefixWord ++ tailWord_2544561) baseStart_2544561 baseEnd_2544561 := by
    simpa [prefixWord, tailWord_2544561, baseEnd_2544561] using wordTrace_append hprefix tailTrace_2544561
  have hstable : (prefixWord ++ tailWord_2544561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544561).length < 2 ^ (prefixWord ++ tailWord_2544561).sum := by decide
  have hdescent : baseEnd_2544561 < baseStart_2544561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544566 : List Nat := [5, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3]
def baseStart_2544566 : Nat := 118140960795 + 2544566 * 2 ^ 59
def prefixEnd_2544566 : Nat := 4983230072969 + 3 ^ 40 * 2544566 * 2
def baseEnd_2544566 : Nat := 1306585415088596607522761

theorem tailTrace_2544566 : CollatzResearch.WordTrace tailWord_2544566 prefixEnd_2544566 1306585415088596607522761 := by
  unfold tailWord_2544566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5800496656217464632465347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61871964332986289412963701 5800496656217464632465347)
  ·
    refine ⟨8700744984326196948698021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5800496656217464632465347 8700744984326196948698021)
    ·
      refine ⟨1631389684561161927880879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8700744984326196948698021 1631389684561161927880879)
      ·
        refine ⟨2447084526841742891821319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1631389684561161927880879 2447084526841742891821319)
        ·
          refine ⟨3670626790262614337731979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2447084526841742891821319 3670626790262614337731979)
          ·
            refine ⟨5505940185393921506597969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3670626790262614337731979 5505940185393921506597969)
            ·
              refine ⟨4129455139045441129948477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5505940185393921506597969 4129455139045441129948477)
              ·
                refine ⟨1548545677142040423730679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4129455139045441129948477 1548545677142040423730679)
                ·
                  refine ⟨2322818515713060635596019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548545677142040423730679 2322818515713060635596019)
                  ·
                    refine ⟨3484227773569590953394029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2322818515713060635596019 3484227773569590953394029)
                    ·
                      refine ⟨1306585415088596607522761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3484227773569590953394029 1306585415088596607522761)
                      ·
                        rfl

theorem cell23_2544566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_2544566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544566 prefixEnd_2544566 := by exact prefixLift 2544566
  have htrace : WordTrace (prefixWord ++ tailWord_2544566) baseStart_2544566 baseEnd_2544566 := by
    simpa [prefixWord, tailWord_2544566, baseEnd_2544566] using wordTrace_append hprefix tailTrace_2544566
  have hstable : (prefixWord ++ tailWord_2544566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544566).length < 2 ^ (prefixWord ++ tailWord_2544566).sum := by decide
  have hdescent : baseEnd_2544566 < baseStart_2544566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544615 : List Nat := [1, 1, 5, 2, 2, 2, 2, 2, 1, 3, 2]
def baseStart_2544615 : Nat := 118140960795 + 2544615 * 2 ^ 59
def prefixEnd_2544615 : Nat := 4983230072969 + 3 ^ 40 * 2544615 * 2
def baseEnd_2544615 : Nat := 1306610575640666915810035

theorem tailTrace_2544615 : CollatzResearch.WordTrace tailWord_2544615 prefixEnd_2544615 1306610575640666915810035 := by
  unfold tailWord_2544615
  simp only [CollatzResearch.WordTrace]
  refine ⟨92809733676301915487979299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61873155784201276991986199 92809733676301915487979299)
  ·
    refine ⟨139214600514452873231968949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92809733676301915487979299 139214600514452873231968949)
    ·
      refine ⟨13051368798229956865497089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139214600514452873231968949 13051368798229956865497089)
      ·
        refine ⟨9788526598672467649122817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13051368798229956865497089 9788526598672467649122817)
        ·
          refine ⟨7341394949004350736842113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9788526598672467649122817 7341394949004350736842113)
          ·
            refine ⟨5506046211753263052631585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7341394949004350736842113 5506046211753263052631585)
            ·
              refine ⟨4129534658814947289473689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5506046211753263052631585 4129534658814947289473689)
              ·
                refine ⟨3097150994111210467105267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4129534658814947289473689 3097150994111210467105267)
                ·
                  refine ⟨4645726491166815700657901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3097150994111210467105267 4645726491166815700657901)
                  ·
                    refine ⟨1742147434187555887746713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4645726491166815700657901 1742147434187555887746713)
                    ·
                      refine ⟨1306610575640666915810035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742147434187555887746713 1306610575640666915810035)
                      ·
                        rfl

theorem cell23_2544615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_2544615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544615 prefixEnd_2544615 := by exact prefixLift 2544615
  have htrace : WordTrace (prefixWord ++ tailWord_2544615) baseStart_2544615 baseEnd_2544615 := by
    simpa [prefixWord, tailWord_2544615, baseEnd_2544615] using wordTrace_append hprefix tailTrace_2544615
  have hstable : (prefixWord ++ tailWord_2544615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544615).length < 2 ^ (prefixWord ++ tailWord_2544615).sum := by decide
  have hdescent : baseEnd_2544615 < baseStart_2544615 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544651 : List Nat := [1, 1, 1, 1, 6, 4, 1, 1, 7]
def baseStart_2544651 : Nat := 118140960795 + 2544651 * 2 ^ 59
def prefixEnd_2544651 : Nat := 4983230072969 + 3 ^ 40 * 2544651 * 2
def baseEnd_2544651 : Nat := 145181006771580974995541

theorem tailTrace_2544651 : CollatzResearch.WordTrace tailWord_2544651 prefixEnd_2544651 145181006771580974995541 := by
  unfold tailWord_2544651
  simp only [CollatzResearch.WordTrace]
  refine ⟨92811046704171493636289807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61874031136114329090859871 92811046704171493636289807)
  ·
    refine ⟨139216570056257240454434711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92811046704171493636289807 139216570056257240454434711)
    ·
      refine ⟨208824855084385860681652067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139216570056257240454434711 208824855084385860681652067)
      ·
        refine ⟨313237282626578791022478101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208824855084385860681652067 313237282626578791022478101)
        ·
          refine ⟨14682997623120880829178661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 313237282626578791022478101 14682997623120880829178661)
          ·
            refine ⟨2753062054335165155470999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14682997623120880829178661 2753062054335165155470999)
            ·
              refine ⟨4129593081502747733206499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753062054335165155470999 4129593081502747733206499)
              ·
                refine ⟨6194389622254121599809749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4129593081502747733206499 6194389622254121599809749)
                ·
                  refine ⟨145181006771580974995541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6194389622254121599809749 145181006771580974995541)
                  ·
                    rfl

theorem cell23_2544651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 7].length) (baseStart_2544651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544651 prefixEnd_2544651 := by exact prefixLift 2544651
  have htrace : WordTrace (prefixWord ++ tailWord_2544651) baseStart_2544651 baseEnd_2544651 := by
    simpa [prefixWord, tailWord_2544651, baseEnd_2544651] using wordTrace_append hprefix tailTrace_2544651
  have hstable : (prefixWord ++ tailWord_2544651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544651).length < 2 ^ (prefixWord ++ tailWord_2544651).sum := by decide
  have hdescent : baseEnd_2544651 < baseStart_2544651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544702 : List Nat := [4, 2, 1, 3, 1, 3, 2, 2, 5]
def baseStart_2544702 : Nat := 118140960795 + 2544702 * 2 ^ 59
def prefixEnd_2544702 : Nat := 4983230072969 + 3 ^ 40 * 2544702 * 2
def baseEnd_2544702 : Nat := 145183916495289786158015

theorem tailTrace_2544702 : CollatzResearch.WordTrace tailWord_2544702 prefixEnd_2544702 145183916495289786158015 := by
  unfold tailWord_2544702
  simp only [CollatzResearch.WordTrace]
  refine ⟨11601613353373341168299545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61875271217991152897597573 11601613353373341168299545)
  ·
    refine ⟨8701210015030005876224659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11601613353373341168299545 8701210015030005876224659)
    ·
      refine ⟨13051815022545008814336989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8701210015030005876224659 13051815022545008814336989)
      ·
        refine ⟨4894430633454378305376371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13051815022545008814336989 4894430633454378305376371)
        ·
          refine ⟨7341645950181567458064557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4894430633454378305376371 7341645950181567458064557)
          ·
            refine ⟨2753117231318087796774209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7341645950181567458064557 2753117231318087796774209)
            ·
              refine ⟨2064837923488565847580657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2753117231318087796774209 2064837923488565847580657)
              ·
                refine ⟨1548628442616424385685493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2064837923488565847580657 1548628442616424385685493)
                ·
                  refine ⟨145183916495289786158015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1548628442616424385685493 145183916495289786158015)
                  ·
                    rfl

theorem cell23_2544702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 2, 5].length) (baseStart_2544702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544702 prefixEnd_2544702 := by exact prefixLift 2544702
  have htrace : WordTrace (prefixWord ++ tailWord_2544702) baseStart_2544702 baseEnd_2544702 := by
    simpa [prefixWord, tailWord_2544702, baseEnd_2544702] using wordTrace_append hprefix tailTrace_2544702
  have hstable : (prefixWord ++ tailWord_2544702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544702).length < 2 ^ (prefixWord ++ tailWord_2544702).sum := by decide
  have hdescent : baseEnd_2544702 < baseStart_2544702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544704 : List Nat := [2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 5]
def baseStart_2544704 : Nat := 118140960795 + 2544704 * 2 ^ 59
def prefixEnd_2544704 : Nat := 4983230072969 + 3 ^ 40 * 2544704 * 2
def baseEnd_2544704 : Nat := 1306656275418917067597125

theorem tailTrace_2544704 : CollatzResearch.WordTrace tailWord_2544704 prefixEnd_2544704 1306656275418917067597125 := by
  unfold tailWord_2544704
  simp only [CollatzResearch.WordTrace]
  refine ⟨46406489886489741843984583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61875319848652989125312777 46406489886489741843984583)
  ·
    refine ⟨69609734829734612765976875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46406489886489741843984583 69609734829734612765976875)
    ·
      refine ⟨104414602244601919148965313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69609734829734612765976875 104414602244601919148965313)
      ·
        refine ⟨78310951683451439361723985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104414602244601919148965313 78310951683451439361723985)
        ·
          refine ⟨58733213762588579521292989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78310951683451439361723985 58733213762588579521292989)
          ·
            refine ⟨22024955160970717320484871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58733213762588579521292989 22024955160970717320484871)
            ·
              refine ⟨33037432741456075980727307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22024955160970717320484871 33037432741456075980727307)
              ·
                refine ⟨49556149112184113971090961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33037432741456075980727307 49556149112184113971090961)
                ·
                  refine ⟨37167111834138085478318221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49556149112184113971090961 37167111834138085478318221)
                  ·
                    refine ⟨13937666937801782054369333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 37167111834138085478318221 13937666937801782054369333)
                    ·
                      refine ⟨1306656275418917067597125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13937666937801782054369333 1306656275418917067597125)
                      ·
                        rfl

theorem cell23_2544704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_2544704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544704 prefixEnd_2544704 := by exact prefixLift 2544704
  have htrace : WordTrace (prefixWord ++ tailWord_2544704) baseStart_2544704 baseEnd_2544704 := by
    simpa [prefixWord, tailWord_2544704, baseEnd_2544704] using wordTrace_append hprefix tailTrace_2544704
  have hstable : (prefixWord ++ tailWord_2544704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544704).length < 2 ^ (prefixWord ++ tailWord_2544704).sum := by decide
  have hdescent : baseEnd_2544704 < baseStart_2544704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544718 : List Nat := [4, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2]
def baseStart_2544718 : Nat := 118140960795 + 2544718 * 2 ^ 59
def prefixEnd_2544718 : Nat := 4983230072969 + 3 ^ 40 * 2544718 * 2
def baseEnd_2544718 : Nat := 1306663464148080012822061

theorem tailTrace_2544718 : CollatzResearch.WordTrace tailWord_2544718 prefixEnd_2544718 1306663464148080012822061 := by
  unfold tailWord_2544718
  simp only [CollatzResearch.WordTrace]
  refine ⟨11601686299366095509872351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61875660263285842719319205 11601686299366095509872351)
  ·
    refine ⟨17402529449049143264808527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11601686299366095509872351 17402529449049143264808527)
    ·
      refine ⟨26103794173573714897212791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17402529449049143264808527 26103794173573714897212791)
      ·
        refine ⟨39155691260360572345819187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26103794173573714897212791 39155691260360572345819187)
        ·
          refine ⟨58733536890540858518728781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39155691260360572345819187 58733536890540858518728781)
          ·
            refine ⟨22025076333952821944523293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58733536890540858518728781 22025076333952821944523293)
            ·
              refine ⟨8259403625232308229196235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22025076333952821944523293 8259403625232308229196235)
              ·
                refine ⟨12389105437848462343794353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8259403625232308229196235 12389105437848462343794353)
                ·
                  refine ⟨9291829078386346757845765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12389105437848462343794353 9291829078386346757845765)
                  ·
                    refine ⟨1742217952197440017096081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9291829078386346757845765 1742217952197440017096081)
                    ·
                      refine ⟨1306663464148080012822061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742217952197440017096081 1306663464148080012822061)
                      ·
                        rfl

theorem cell23_2544718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_2544718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544718 prefixEnd_2544718 := by exact prefixLift 2544718
  have htrace : WordTrace (prefixWord ++ tailWord_2544718) baseStart_2544718 baseEnd_2544718 := by
    simpa [prefixWord, tailWord_2544718, baseEnd_2544718] using wordTrace_append hprefix tailTrace_2544718
  have hstable : (prefixWord ++ tailWord_2544718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544718).length < 2 ^ (prefixWord ++ tailWord_2544718).sum := by decide
  have hdescent : baseEnd_2544718 < baseStart_2544718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544721 : List Nat := [1, 2, 2, 1, 3, 1, 2, 2, 4, 2, 3]
def baseStart_2544721 : Nat := 118140960795 + 2544721 * 2 ^ 59
def prefixEnd_2544721 : Nat := 4983230072969 + 3 ^ 40 * 2544721 * 2
def baseEnd_2544721 : Nat := 1306665004590043501084547

theorem tailTrace_2544721 : CollatzResearch.WordTrace tailWord_2544721 prefixEnd_2544721 1306665004590043501084547 := by
  unfold tailWord_2544721
  simp only [CollatzResearch.WordTrace]
  refine ⟨92813599813917895591338017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61875733209278597060892011 92813599813917895591338017)
  ·
    refine ⟨69610199860438421693503513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92813599813917895591338017 69610199860438421693503513)
    ·
      refine ⟨52207649895328816270127635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69610199860438421693503513 52207649895328816270127635)
      ·
        refine ⟨78311474842993224405191453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52207649895328816270127635 78311474842993224405191453)
        ·
          refine ⟨29366803066122459151946795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78311474842993224405191453 29366803066122459151946795)
          ·
            refine ⟨44050204599183688727920193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29366803066122459151946795 44050204599183688727920193)
            ·
              refine ⟨33037653449387766545940145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44050204599183688727920193 33037653449387766545940145)
              ·
                refine ⟨24778240087040824909455109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33037653449387766545940145 24778240087040824909455109)
                ·
                  refine ⟨4645920016320154670522833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24778240087040824909455109 4645920016320154670522833)
                  ·
                    refine ⟨3484440012240116002892125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4645920016320154670522833 3484440012240116002892125)
                    ·
                      refine ⟨1306665004590043501084547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3484440012240116002892125 1306665004590043501084547)
                      ·
                        rfl

theorem cell23_2544721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_2544721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544721 prefixEnd_2544721 := by exact prefixLift 2544721
  have htrace : WordTrace (prefixWord ++ tailWord_2544721) baseStart_2544721 baseEnd_2544721 := by
    simpa [prefixWord, tailWord_2544721, baseEnd_2544721] using wordTrace_append hprefix tailTrace_2544721
  have hstable : (prefixWord ++ tailWord_2544721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544721).length < 2 ^ (prefixWord ++ tailWord_2544721).sum := by decide
  have hdescent : baseEnd_2544721 < baseStart_2544721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544745 : List Nat := [1, 2, 1, 1, 1, 7, 2, 3, 1, 4]
def baseStart_2544745 : Nat := 118140960795 + 2544745 * 2 ^ 59
def prefixEnd_2544745 : Nat := 4983230072969 + 3 ^ 40 * 2544745 * 2
def baseEnd_2544745 : Nat := 435559109375250469061479

theorem tailTrace_2544745 : CollatzResearch.WordTrace tailWord_2544745 prefixEnd_2544745 435559109375250469061479 := by
  unfold tailWord_2544745
  simp only [CollatzResearch.WordTrace]
  refine ⟨92814475165830947690211689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61876316777220631793474459 92814475165830947690211689)
  ·
    refine ⟨69610856374373210767658767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92814475165830947690211689 69610856374373210767658767)
    ·
      refine ⟨104416284561559816151488151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69610856374373210767658767 104416284561559816151488151)
      ·
        refine ⟨156624426842339724227232227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104416284561559816151488151 156624426842339724227232227)
        ·
          refine ⟨234936640263509586340848341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156624426842339724227232227 234936640263509586340848341)
          ·
            refine ⟨5506327506176005929863633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 234936640263509586340848341 5506327506176005929863633)
            ·
              refine ⟨4129745629632004447397725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5506327506176005929863633 4129745629632004447397725)
              ·
                refine ⟨1548654611112001667774147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4129745629632004447397725 1548654611112001667774147)
                ·
                  refine ⟨2322981916668002501661221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548654611112001667774147 2322981916668002501661221)
                  ·
                    refine ⟨435559109375250469061479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2322981916668002501661221 435559109375250469061479)
                    ·
                      rfl

theorem cell23_2544745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 1, 4].length) (baseStart_2544745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544745 prefixEnd_2544745 := by exact prefixLift 2544745
  have htrace : WordTrace (prefixWord ++ tailWord_2544745) baseStart_2544745 baseEnd_2544745 := by
    simpa [prefixWord, tailWord_2544745, baseEnd_2544745] using wordTrace_append hprefix tailTrace_2544745
  have hstable : (prefixWord ++ tailWord_2544745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544745).length < 2 ^ (prefixWord ++ tailWord_2544745).sum := by decide
  have hdescent : baseEnd_2544745 < baseStart_2544745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544768 : List Nat := [2, 1, 1, 2, 1, 3, 3, 3, 3, 1, 3]
def baseStart_2544768 : Nat := 118140960795 + 2544768 * 2 ^ 59
def prefixEnd_2544768 : Nat := 4983230072969 + 3 ^ 40 * 2544768 * 2
def baseEnd_2544768 : Nat := 1306689138180804817196831

theorem tailTrace_2544768 : CollatzResearch.WordTrace tailWord_2544768 prefixEnd_2544768 1306689138180804817196831 := by
  unfold tailWord_2544768
  simp only [CollatzResearch.WordTrace]
  refine ⟨46407657022373811309149479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61876876029831748412199305 46407657022373811309149479)
  ·
    refine ⟨69611485533560716963724219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46407657022373811309149479 69611485533560716963724219)
    ·
      refine ⟨104417228300341075445586329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69611485533560716963724219 104417228300341075445586329)
      ·
        refine ⟨78312921225255806584189747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104417228300341075445586329 78312921225255806584189747)
        ·
          refine ⟨117469381837883709876284621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78312921225255806584189747 117469381837883709876284621)
          ·
            refine ⟨44051018189206391203606733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117469381837883709876284621 44051018189206391203606733)
            ·
              refine ⟨16519131820952396701352525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 44051018189206391203606733 16519131820952396701352525)
              ·
                refine ⟨6194674432857148763007197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16519131820952396701352525 6194674432857148763007197)
                ·
                  refine ⟨2323002912321430786127699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6194674432857148763007197 2323002912321430786127699)
                  ·
                    refine ⟨3484504368482146179191549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2323002912321430786127699 3484504368482146179191549)
                    ·
                      refine ⟨1306689138180804817196831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3484504368482146179191549 1306689138180804817196831)
                      ·
                        rfl

theorem cell23_2544768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 3, 3, 1, 3].length) (baseStart_2544768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544768 prefixEnd_2544768 := by exact prefixLift 2544768
  have htrace : WordTrace (prefixWord ++ tailWord_2544768) baseStart_2544768 baseEnd_2544768 := by
    simpa [prefixWord, tailWord_2544768, baseEnd_2544768] using wordTrace_append hprefix tailTrace_2544768
  have hstable : (prefixWord ++ tailWord_2544768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544768).length < 2 ^ (prefixWord ++ tailWord_2544768).sum := by decide
  have hdescent : baseEnd_2544768 < baseStart_2544768 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544778 : List Nat := [3, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2]
def baseStart_2544778 : Nat := 118140960795 + 2544778 * 2 ^ 59
def prefixEnd_2544778 : Nat := 4983230072969 + 3 ^ 40 * 2544778 * 2
def baseEnd_2544778 : Nat := 1306694272987349778071785

theorem tailTrace_2544778 : CollatzResearch.WordTrace tailWord_2544778 prefixEnd_2544778 1306694272987349778071785 := by
  unfold tailWord_2544778
  simp only [CollatzResearch.WordTrace]
  refine ⟨23203919693677848581540747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61877119183140929550775325 23203919693677848581540747)
  ·
    refine ⟨34805879540516772872311121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23203919693677848581540747 34805879540516772872311121)
    ·
      refine ⟨26104409655387579654233341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34805879540516772872311121 26104409655387579654233341)
      ·
        refine ⟨9789153620770342370337503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26104409655387579654233341 9789153620770342370337503)
        ·
          refine ⟨14683730431155513555506255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9789153620770342370337503 14683730431155513555506255)
          ·
            refine ⟨22025595646733270333259383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14683730431155513555506255 22025595646733270333259383)
            ·
              refine ⟨33038393470099905499889075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22025595646733270333259383 33038393470099905499889075)
              ·
                refine ⟨49557590205149858249833613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33038393470099905499889075 49557590205149858249833613)
                ·
                  refine ⟨18584096326931196843687605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49557590205149858249833613 18584096326931196843687605)
                  ·
                    refine ⟨1742259030649799704095713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18584096326931196843687605 1742259030649799704095713)
                    ·
                      refine ⟨1306694272987349778071785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742259030649799704095713 1306694272987349778071785)
                      ·
                        rfl

theorem cell23_2544778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_2544778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544778 prefixEnd_2544778 := by exact prefixLift 2544778
  have htrace : WordTrace (prefixWord ++ tailWord_2544778) baseStart_2544778 baseEnd_2544778 := by
    simpa [prefixWord, tailWord_2544778, baseEnd_2544778] using wordTrace_append hprefix tailTrace_2544778
  have hstable : (prefixWord ++ tailWord_2544778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544778).length < 2 ^ (prefixWord ++ tailWord_2544778).sum := by decide
  have hdescent : baseEnd_2544778 < baseStart_2544778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544801 : List Nat := [1, 2, 3, 3, 1, 1, 2, 1, 3, 6]
def baseStart_2544801 : Nat := 118140960795 + 2544801 * 2 ^ 59
def prefixEnd_2544801 : Nat := 4983230072969 + 3 ^ 40 * 2544801 * 2
def baseEnd_2544801 : Nat := 435568694347467729361393

theorem tailTrace_2544801 : CollatzResearch.WordTrace tailWord_2544801 prefixEnd_2544801 435568694347467729361393 := by
  unfold tailWord_2544801
  simp only [CollatzResearch.WordTrace]
  refine ⟨92816517653628069254250257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61877678435752046169500171 92816517653628069254250257)
  ·
    refine ⟨69612388240221051940687693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92816517653628069254250257 69612388240221051940687693)
    ·
      refine ⟨26104645590082894477757885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69612388240221051940687693 26104645590082894477757885)
      ·
        refine ⟨9789242096281085429159207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26104645590082894477757885 9789242096281085429159207)
        ·
          refine ⟨14683863144421628143738811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9789242096281085429159207 14683863144421628143738811)
          ·
            refine ⟨22025794716632442215608217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14683863144421628143738811 22025794716632442215608217)
            ·
              refine ⟨16519346037474331661706163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22025794716632442215608217 16519346037474331661706163)
              ·
                refine ⟨24779019056211497492559245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16519346037474331661706163 24779019056211497492559245)
                ·
                  refine ⟨9292132146079311559709717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24779019056211497492559245 9292132146079311559709717)
                  ·
                    refine ⟨435568694347467729361393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9292132146079311559709717 435568694347467729361393)
                    ·
                      rfl

theorem cell23_2544801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_2544801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544801 prefixEnd_2544801 := by exact prefixLift 2544801
  have htrace : WordTrace (prefixWord ++ tailWord_2544801) baseStart_2544801 baseEnd_2544801 := by
    simpa [prefixWord, tailWord_2544801, baseEnd_2544801] using wordTrace_append hprefix tailTrace_2544801
  have hstable : (prefixWord ++ tailWord_2544801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544801).length < 2 ^ (prefixWord ++ tailWord_2544801).sum := by decide
  have hdescent : baseEnd_2544801 < baseStart_2544801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544818 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 4, 4]
def baseStart_2544818 : Nat := 118140960795 + 2544818 * 2 ^ 59
def prefixEnd_2544818 : Nat := 4983230072969 + 3 ^ 40 * 2544818 * 2
def baseEnd_2544818 : Nat := 435571604071176540523867

theorem tailTrace_2544818 : CollatzResearch.WordTrace tailWord_2544818 prefixEnd_2544818 435571604071176540523867 := by
  unfold tailWord_2544818
  simp only [CollatzResearch.WordTrace]
  refine ⟨23204284423641620289404777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61878091796377654105079405 23204284423641620289404777)
  ·
    refine ⟨17403213317731215217053583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23204284423641620289404777 17403213317731215217053583)
    ·
      refine ⟨26104819976596822825580375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17403213317731215217053583 26104819976596822825580375)
      ·
        refine ⟨39157229964895234238370563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26104819976596822825580375 39157229964895234238370563)
        ·
          refine ⟨58735844947342851357555845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39157229964895234238370563 58735844947342851357555845)
          ·
            refine ⟨11012970927626784629541721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58735844947342851357555845 11012970927626784629541721)
            ·
              refine ⟨8259728195720088472156291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11012970927626784629541721 8259728195720088472156291)
              ·
                refine ⟨12389592293580132708234437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8259728195720088472156291 12389592293580132708234437)
                ·
                  refine ⟨2323048555046274882793957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12389592293580132708234437 2323048555046274882793957)
                  ·
                    refine ⟨435571604071176540523867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2323048555046274882793957 435571604071176540523867)
                    ·
                      rfl

theorem cell23_2544818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4, 4].length) (baseStart_2544818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544818 prefixEnd_2544818 := by exact prefixLift 2544818
  have htrace : WordTrace (prefixWord ++ tailWord_2544818) baseStart_2544818 baseEnd_2544818 := by
    simpa [prefixWord, tailWord_2544818, baseEnd_2544818] using wordTrace_append hprefix tailTrace_2544818
  have hstable : (prefixWord ++ tailWord_2544818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544818).length < 2 ^ (prefixWord ++ tailWord_2544818).sum := by decide
  have hdescent : baseEnd_2544818 < baseStart_2544818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544828 : List Nat := [2, 2, 2, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_2544828 : Nat := 118140960795 + 2544828 * 2 ^ 59
def prefixEnd_2544828 : Nat := 4983230072969 + 3 ^ 40 * 2544828 * 2
def baseEnd_2544828 : Nat := 1306719947020074582446555

theorem tailTrace_2544828 : CollatzResearch.WordTrace tailWord_2544828 prefixEnd_2544828 1306719947020074582446555 := by
  unfold tailWord_2544828
  simp only [CollatzResearch.WordTrace]
  refine ⟨46408751212265126432741569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61878334949686835243655425 46408751212265126432741569)
  ·
    refine ⟨34806563409198844824556177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46408751212265126432741569 34806563409198844824556177)
    ·
      refine ⟨26104922556899133618417133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34806563409198844824556177 26104922556899133618417133)
      ·
        refine ⟨9789345958837175106906425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26104922556899133618417133 9789345958837175106906425)
        ·
          refine ⟨7342009469127881330179819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9789345958837175106906425 7342009469127881330179819)
          ·
            refine ⟨11013014203691821995269729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7342009469127881330179819 11013014203691821995269729)
            ·
              refine ⟨8259760652768866496452297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11013014203691821995269729 8259760652768866496452297)
              ·
                refine ⟨6194820489576649872339223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8259760652768866496452297 6194820489576649872339223)
                ·
                  refine ⟨9292230734364974808508835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6194820489576649872339223 9292230734364974808508835)
                  ·
                    refine ⟨13938346101547462212763253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9292230734364974808508835 13938346101547462212763253)
                    ·
                      refine ⟨1306719947020074582446555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13938346101547462212763253 1306719947020074582446555)
                      ·
                        rfl

theorem cell23_2544828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_2544828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544828 prefixEnd_2544828 := by exact prefixLift 2544828
  have htrace : WordTrace (prefixWord ++ tailWord_2544828) baseStart_2544828 baseEnd_2544828 := by
    simpa [prefixWord, tailWord_2544828, baseEnd_2544828] using wordTrace_append hprefix tailTrace_2544828
  have hstable : (prefixWord ++ tailWord_2544828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544828).length < 2 ^ (prefixWord ++ tailWord_2544828).sum := by decide
  have hdescent : baseEnd_2544828 < baseStart_2544828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544875 : List Nat := [1, 1, 1, 1, 2, 6, 1, 4, 2, 1, 3]
def baseStart_2544875 : Nat := 118140960795 + 2544875 * 2 ^ 59
def prefixEnd_2544875 : Nat := 4983230072969 + 3 ^ 40 * 2544875 * 2
def baseEnd_2544875 : Nat := 1306744080610835898558839

theorem tailTrace_2544875 : CollatzResearch.WordTrace tailWord_2544875 prefixEnd_2544875 1306744080610835898558839 := by
  unfold tailWord_2544875
  simp only [CollatzResearch.WordTrace]
  refine ⟨92819216655359979892444079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61879477770239986594962719 92819216655359979892444079)
  ·
    refine ⟨139228824983039969838666119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92819216655359979892444079 139228824983039969838666119)
    ·
      refine ⟨208843237474559954757999179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139228824983039969838666119 208843237474559954757999179)
      ·
        refine ⟨313264856211839932136998769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208843237474559954757999179 313264856211839932136998769)
        ·
          refine ⟨234948642158879949102749077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 313264856211839932136998769 234948642158879949102749077)
          ·
            refine ⟨11013217601197497614191363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 234948642158879949102749077 11013217601197497614191363)
            ·
              refine ⟨16519826401796246421287045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11013217601197497614191363 16519826401796246421287045)
              ·
                refine ⟨3097467450336796203991321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16519826401796246421287045 3097467450336796203991321)
                ·
                  refine ⟨2323100587752597152993491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3097467450336796203991321 2323100587752597152993491)
                  ·
                    refine ⟨3484650881628895729490237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2323100587752597152993491 3484650881628895729490237)
                    ·
                      refine ⟨1306744080610835898558839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3484650881628895729490237 1306744080610835898558839)
                      ·
                        rfl

theorem cell23_2544875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 4, 2, 1, 3].length) (baseStart_2544875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544875 prefixEnd_2544875 := by exact prefixLift 2544875
  have htrace : WordTrace (prefixWord ++ tailWord_2544875) baseStart_2544875 baseEnd_2544875 := by
    simpa [prefixWord, tailWord_2544875, baseEnd_2544875] using wordTrace_append hprefix tailTrace_2544875
  have hstable : (prefixWord ++ tailWord_2544875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544875).length < 2 ^ (prefixWord ++ tailWord_2544875).sum := by decide
  have hdescent : baseEnd_2544875 < baseStart_2544875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544876 : List Nat := [2, 2, 1, 1, 2, 6, 2, 2, 1, 2, 2]
def baseStart_2544876 : Nat := 118140960795 + 2544876 * 2 ^ 59
def prefixEnd_2544876 : Nat := 4983230072969 + 3 ^ 40 * 2544876 * 2
def baseEnd_2544876 : Nat := 1306744594091490394646335

theorem tailTrace_2544876 : CollatzResearch.WordTrace tailWord_2544876 prefixEnd_2544876 1306744594091490394646335 := by
  unfold tailWord_2544876
  simp only [CollatzResearch.WordTrace]
  refine ⟨46409626564178178531615241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61879502085570904708820321 46409626564178178531615241)
  ·
    refine ⟨34807219923133633898711431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46409626564178178531615241 34807219923133633898711431)
    ·
      refine ⟨52210829884700450848067147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34807219923133633898711431 52210829884700450848067147)
      ·
        refine ⟨78316244827050676272100721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52210829884700450848067147 78316244827050676272100721)
        ·
          refine ⟨58737183620288007204075541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78316244827050676272100721 58737183620288007204075541)
          ·
            refine ⟨2753305482201000337691041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 58737183620288007204075541 2753305482201000337691041)
            ·
              refine ⟨2064979111650750253268281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2753305482201000337691041 2064979111650750253268281)
              ·
                refine ⟨1548734333738062689951211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2064979111650750253268281 1548734333738062689951211)
                ·
                  refine ⟨2323101500607094034926817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548734333738062689951211 2323101500607094034926817)
                  ·
                    refine ⟨1742326125455320526195113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2323101500607094034926817 1742326125455320526195113)
                    ·
                      refine ⟨1306744594091490394646335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742326125455320526195113 1306744594091490394646335)
                      ·
                        rfl

theorem cell23_2544876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 2, 1, 2, 2].length) (baseStart_2544876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544876 prefixEnd_2544876 := by exact prefixLift 2544876
  have htrace : WordTrace (prefixWord ++ tailWord_2544876) baseStart_2544876 baseEnd_2544876 := by
    simpa [prefixWord, tailWord_2544876, baseEnd_2544876] using wordTrace_append hprefix tailTrace_2544876
  have hstable : (prefixWord ++ tailWord_2544876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544876).length < 2 ^ (prefixWord ++ tailWord_2544876).sum := by decide
  have hdescent : baseEnd_2544876 < baseStart_2544876 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544932 : List Nat := [2, 3, 1, 3, 1, 1, 3, 1, 4, 2, 2]
def baseStart_2544932 : Nat := 118140960795 + 2544932 * 2 ^ 59
def prefixEnd_2544932 : Nat := 4983230072969 + 3 ^ 40 * 2544932 * 2
def baseEnd_2544932 : Nat := 1306773349008142175546077

theorem tailTrace_2544932 : CollatzResearch.WordTrace tailWord_2544932 prefixEnd_2544932 1306773349008142175546077 := by
  unfold tailWord_2544932
  simp only [CollatzResearch.WordTrace]
  refine ⟨46410647808076739313634525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61880863744102319084846033 46410647808076739313634525)
  ·
    refine ⟨17403992928028777242612947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46410647808076739313634525 17403992928028777242612947)
    ·
      refine ⟨26105989392043165863919421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17403992928028777242612947 26105989392043165863919421)
      ·
        refine ⟨9789746022016187198969783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26105989392043165863919421 9789746022016187198969783)
        ·
          refine ⟨14684619033024280798454675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9789746022016187198969783 14684619033024280798454675)
          ·
            refine ⟨22026928549536421197682013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14684619033024280798454675 22026928549536421197682013)
            ·
              refine ⟨8260098206076157949130755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22026928549536421197682013 8260098206076157949130755)
              ·
                refine ⟨12390147309114236923696133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8260098206076157949130755 12390147309114236923696133)
                ·
                  refine ⟨2323152620458919423193025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12390147309114236923696133 2323152620458919423193025)
                  ·
                    refine ⟨1742364465344189567394769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2323152620458919423193025 1742364465344189567394769)
                    ·
                      refine ⟨1306773349008142175546077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742364465344189567394769 1306773349008142175546077)
                      ·
                        rfl

theorem cell23_2544932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_2544932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544932 prefixEnd_2544932 := by exact prefixLift 2544932
  have htrace : WordTrace (prefixWord ++ tailWord_2544932) baseStart_2544932 baseEnd_2544932 := by
    simpa [prefixWord, tailWord_2544932, baseEnd_2544932] using wordTrace_append hprefix tailTrace_2544932
  have hstable : (prefixWord ++ tailWord_2544932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544932).length < 2 ^ (prefixWord ++ tailWord_2544932).sum := by decide
  have hdescent : baseEnd_2544932 < baseStart_2544932 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544968 : List Nat := [2, 1, 3, 1, 1, 2, 1, 5, 2, 5]
def baseStart_2544968 : Nat := 118140960795 + 2544968 * 2 ^ 59
def prefixEnd_2544968 : Nat := 4983230072969 + 3 ^ 40 * 2544968 * 2
def baseEnd_2544968 : Nat := 435597278103901344898637

theorem tailTrace_2544968 : CollatzResearch.WordTrace tailWord_2544968 prefixEnd_2544968 435597278103901344898637 := by
  unfold tailWord_2544968
  simp only [CollatzResearch.WordTrace]
  refine ⟨46411304322011528387789779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61881739096015371183719705 46411304322011528387789779)
  ·
    refine ⟨69616956483017292581684669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46411304322011528387789779 69616956483017292581684669)
    ·
      refine ⟨26106358681131484718131751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69616956483017292581684669 26106358681131484718131751)
      ·
        refine ⟨39159538021697227077197627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26106358681131484718131751 39159538021697227077197627)
        ·
          refine ⟨58739307032545840615796441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39159538021697227077197627 58739307032545840615796441)
          ·
            refine ⟨44054480274409380461847331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58739307032545840615796441 44054480274409380461847331)
            ·
              refine ⟨66081720411614070692770997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44054480274409380461847331 66081720411614070692770997)
              ·
                refine ⟨6195161288588819127447281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66081720411614070692770997 6195161288588819127447281)
                ·
                  refine ⟨4646370966441614345585461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6195161288588819127447281 4646370966441614345585461)
                  ·
                    refine ⟨435597278103901344898637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4646370966441614345585461 435597278103901344898637)
                    ·
                      rfl

theorem cell23_2544968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 5].length) (baseStart_2544968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544968 prefixEnd_2544968 := by exact prefixLift 2544968
  have htrace : WordTrace (prefixWord ++ tailWord_2544968) baseStart_2544968 baseEnd_2544968 := by
    simpa [prefixWord, tailWord_2544968, baseEnd_2544968] using wordTrace_append hprefix tailTrace_2544968
  have hstable : (prefixWord ++ tailWord_2544968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544968).length < 2 ^ (prefixWord ++ tailWord_2544968).sum := by decide
  have hdescent : baseEnd_2544968 < baseStart_2544968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544971 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 8]
def baseStart_2544971 : Nat := 118140960795 + 2544971 * 2 ^ 59
def prefixEnd_2544971 : Nat := 4983230072969 + 3 ^ 40 * 2544971 * 2
def baseEnd_2544971 : Nat := 1306793374753667522958397

theorem tailTrace_2544971 : CollatzResearch.WordTrace tailWord_2544971 prefixEnd_2544971 1306793374753667522958397 := by
  unfold tailWord_2544971
  simp only [CollatzResearch.WordTrace]
  refine ⟨92822718063012188287938767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61881812042008125525292511 92822718063012188287938767)
  ·
    refine ⟨139234077094518282431908151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92822718063012188287938767 139234077094518282431908151)
    ·
      refine ⟨208851115641777423647862227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139234077094518282431908151 208851115641777423647862227)
      ·
        refine ⟨313276673462666135471793341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208851115641777423647862227 313276673462666135471793341)
        ·
          refine ⟨117478752548499800801922503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313276673462666135471793341 117478752548499800801922503)
          ·
            refine ⟨176218128822749701202883755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117478752548499800801922503 176218128822749701202883755)
            ·
              refine ⟨264327193234124551804325633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176218128822749701202883755 264327193234124551804325633)
              ·
                refine ⟨198245394925593413853244225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264327193234124551804325633 198245394925593413853244225)
                ·
                  refine ⟨148684046194195060389933169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198245394925593413853244225 148684046194195060389933169)
                  ·
                    refine ⟨111513034645646295292449877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 148684046194195060389933169 111513034645646295292449877)
                    ·
                      refine ⟨1306793374753667522958397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 111513034645646295292449877 1306793374753667522958397)
                      ·
                        rfl

theorem cell23_2544971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_2544971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544971 prefixEnd_2544971 := by exact prefixLift 2544971
  have htrace : WordTrace (prefixWord ++ tailWord_2544971) baseStart_2544971 baseEnd_2544971 := by
    simpa [prefixWord, tailWord_2544971, baseEnd_2544971] using wordTrace_append hprefix tailTrace_2544971
  have hstable : (prefixWord ++ tailWord_2544971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544971).length < 2 ^ (prefixWord ++ tailWord_2544971).sum := by decide
  have hdescent : baseEnd_2544971 < baseStart_2544971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544972 : List Nat := [2, 2, 1, 3, 2, 4, 1, 3, 5]
def baseStart_2544972 : Nat := 118140960795 + 2544972 * 2 ^ 59
def prefixEnd_2544972 : Nat := 4983230072969 + 3 ^ 40 * 2544972 * 2
def baseEnd_2544972 : Nat := 145199320914924668782877

theorem tailTrace_2544972 : CollatzResearch.WordTrace tailWord_2544972 prefixEnd_2544972 145199320914924668782877 := by
  unfold tailWord_2544972
  simp only [CollatzResearch.WordTrace]
  refine ⟨46411377268004282729362585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61881836357339043639150113 46411377268004282729362585)
  ·
    refine ⟨34808532951003212047021939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46411377268004282729362585 34808532951003212047021939)
    ·
      refine ⟨52212799426504818070532909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34808532951003212047021939 52212799426504818070532909)
      ·
        refine ⟨19579799784939306776449841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52212799426504818070532909 19579799784939306776449841)
        ·
          refine ⟨14684849838704480082337381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19579799784939306776449841 14684849838704480082337381)
          ·
            refine ⟨2753409344757090015438259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14684849838704480082337381 2753409344757090015438259)
            ·
              refine ⟨4130114017135635023157389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753409344757090015438259 4130114017135635023157389)
              ·
                refine ⟨1548792756425863133684021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4130114017135635023157389 1548792756425863133684021)
                ·
                  refine ⟨145199320914924668782877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1548792756425863133684021 145199320914924668782877)
                  ·
                    rfl

theorem cell23_2544972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 5].length) (baseStart_2544972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544972 prefixEnd_2544972 := by exact prefixLift 2544972
  have htrace : WordTrace (prefixWord ++ tailWord_2544972) baseStart_2544972 baseEnd_2544972 := by
    simpa [prefixWord, tailWord_2544972, baseEnd_2544972] using wordTrace_append hprefix tailTrace_2544972
  have hstable : (prefixWord ++ tailWord_2544972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544972).length < 2 ^ (prefixWord ++ tailWord_2544972).sum := by decide
  have hdescent : baseEnd_2544972 < baseStart_2544972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2544978 : List Nat := [3, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_2544978 : Nat := 118140960795 + 2544978 * 2 ^ 59
def prefixEnd_2544978 : Nat := 4983230072969 + 3 ^ 40 * 2544978 * 2
def baseEnd_2544978 : Nat := 1306796969118248995570865

theorem tailTrace_2544978 : CollatzResearch.WordTrace tailWord_2544978 prefixEnd_2544978 1306796969118248995570865 := by
  unfold tailWord_2544978
  simp only [CollatzResearch.WordTrace]
  refine ⟨23205743343496707120860897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61881982249324552322295725 23205743343496707120860897)
  ·
    refine ⟨17404307507622530340645673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23205743343496707120860897 17404307507622530340645673)
    ·
      refine ⟨13053230630716897755484255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17404307507622530340645673 13053230630716897755484255)
      ·
        refine ⟨19579845946075346633226383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13053230630716897755484255 19579845946075346633226383)
        ·
          refine ⟨29369768919113019949839575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19579845946075346633226383 29369768919113019949839575)
          ·
            refine ⟨44054653378669529924759363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29369768919113019949839575 44054653378669529924759363)
            ·
              refine ⟨66081980068004294887139045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44054653378669529924759363 66081980068004294887139045)
              ·
                refine ⟨12390371262750805291338571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66081980068004294887139045 12390371262750805291338571)
                ·
                  refine ⟨18585556894126207937007857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12390371262750805291338571 18585556894126207937007857)
                  ·
                    refine ⟨13939167670594655952755893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18585556894126207937007857 13939167670594655952755893)
                    ·
                      refine ⟨1306796969118248995570865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13939167670594655952755893 1306796969118248995570865)
                      ·
                        rfl

theorem cell23_2544978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_2544978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2544978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2544978 prefixEnd_2544978 := by exact prefixLift 2544978
  have htrace : WordTrace (prefixWord ++ tailWord_2544978) baseStart_2544978 baseEnd_2544978 := by
    simpa [prefixWord, tailWord_2544978, baseEnd_2544978] using wordTrace_append hprefix tailTrace_2544978
  have hstable : (prefixWord ++ tailWord_2544978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2544978).length < 2 ^ (prefixWord ++ tailWord_2544978).sum := by decide
  have hdescent : baseEnd_2544978 < baseStart_2544978 := by decide
  rcases family_descends (prefixWord ++ tailWord_2544978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545049 : List Nat := [1, 2, 1, 2, 1, 5, 4, 2, 1, 4]
def baseStart_2545049 : Nat := 118140960795 + 2545049 * 2 ^ 59
def prefixEnd_2545049 : Nat := 4983230072969 + 3 ^ 40 * 2545049 * 2
def baseEnd_2545049 : Nat := 435611142081572739261013

theorem tailTrace_2545049 : CollatzResearch.WordTrace tailWord_2545049 prefixEnd_2545049 435611142081572739261013 := by
  unfold tailWord_2545049
  simp only [CollatzResearch.WordTrace]
  refine ⟨92825562956729607609278201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61883708637819738406185467 92825562956729607609278201)
  ·
    refine ⟨69619172217547205706958651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92825562956729607609278201 69619172217547205706958651)
    ·
      refine ⟨104428758326320808560437977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69619172217547205706958651 104428758326320808560437977)
      ·
        refine ⟨78321568744740606420328483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104428758326320808560437977 78321568744740606420328483)
        ·
          refine ⟨117482353117110909630492725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78321568744740606420328483 117482353117110909630492725)
          ·
            refine ⟨11013970604729147777858693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117482353117110909630492725 11013970604729147777858693)
            ·
              refine ⟨2065119488386715208348505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11013970604729147777858693 2065119488386715208348505)
              ·
                refine ⟨1548839616290036406261379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2065119488386715208348505 1548839616290036406261379)
                ·
                  refine ⟨2323259424435054609392069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1548839616290036406261379 2323259424435054609392069)
                  ·
                    refine ⟨435611142081572739261013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2323259424435054609392069 435611142081572739261013)
                    ·
                      rfl

theorem cell23_2545049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 1, 4].length) (baseStart_2545049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545049 prefixEnd_2545049 := by exact prefixLift 2545049
  have htrace : WordTrace (prefixWord ++ tailWord_2545049) baseStart_2545049 baseEnd_2545049 := by
    simpa [prefixWord, tailWord_2545049, baseEnd_2545049] using wordTrace_append hprefix tailTrace_2545049
  have hstable : (prefixWord ++ tailWord_2545049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545049).length < 2 ^ (prefixWord ++ tailWord_2545049).sum := by decide
  have hdescent : baseEnd_2545049 < baseStart_2545049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545135 : List Nat := [1, 1, 2, 1, 4, 1, 6, 7]
def baseStart_2545135 : Nat := 118140960795 + 2545135 * 2 ^ 59
def prefixEnd_2545135 : Nat := 4983230072969 + 3 ^ 40 * 2545135 * 2
def baseEnd_2545135 : Nat := 48402873540037217826209

theorem tailTrace_2545135 : CollatzResearch.WordTrace tailWord_2545135 prefixEnd_2545135 48402873540037217826209 := by
  unfold tailWord_2545135
  simp only [CollatzResearch.WordTrace]
  refine ⟨92828699634418044296908859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61885799756278696197939239 92828699634418044296908859)
  ·
    refine ⟨139243049451627066445363289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92828699634418044296908859 139243049451627066445363289)
    ·
      refine ⟨104432287088720299834022467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139243049451627066445363289 104432287088720299834022467)
      ·
        refine ⟨156648430633080449751033701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104432287088720299834022467 156648430633080449751033701)
        ·
          refine ⟨29371580743702584328318819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 156648430633080449751033701 29371580743702584328318819)
          ·
            refine ⟨44057371115553876492478229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29371580743702584328318819 44057371115553876492478229)
            ·
              refine ⟨2065189271041587960584917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44057371115553876492478229 2065189271041587960584917)
              ·
                refine ⟨48402873540037217826209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2065189271041587960584917 48402873540037217826209)
                ·
                  rfl

theorem cell23_2545135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 6, 7].length) (baseStart_2545135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545135 prefixEnd_2545135 := by exact prefixLift 2545135
  have htrace : WordTrace (prefixWord ++ tailWord_2545135) baseStart_2545135 baseEnd_2545135 := by
    simpa [prefixWord, tailWord_2545135, baseEnd_2545135] using wordTrace_append hprefix tailTrace_2545135
  have hstable : (prefixWord ++ tailWord_2545135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545135).length < 2 ^ (prefixWord ++ tailWord_2545135).sum := by decide
  have hdescent : baseEnd_2545135 < baseStart_2545135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545145 : List Nat := [1, 2, 1, 3, 1, 2, 1, 3, 3, 3, 3]
def baseStart_2545145 : Nat := 118140960795 + 2545145 * 2 ^ 59
def prefixEnd_2545145 : Nat := 4983230072969 + 3 ^ 40 * 2545145 * 2
def baseEnd_2545145 : Nat := 1306882720387549842182597

theorem tailTrace_2545145 : CollatzResearch.WordTrace tailWord_2545145 prefixEnd_2545145 1306882720387549842182597 := by
  unfold tailWord_2545145
  simp only [CollatzResearch.WordTrace]
  refine ⟨92829064364381816004772889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61886042909587877336515259 92829064364381816004772889)
  ·
    refine ⟨69621798273286362003579667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92829064364381816004772889 69621798273286362003579667)
    ·
      refine ⟨104432697409929543005369501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69621798273286362003579667 104432697409929543005369501)
      ·
        refine ⟨39162261528723578627013563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104432697409929543005369501 39162261528723578627013563)
        ·
          refine ⟨58743392293085367940520345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39162261528723578627013563 58743392293085367940520345)
          ·
            refine ⟨44057544219814025955390259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58743392293085367940520345 44057544219814025955390259)
            ·
              refine ⟨66086316329721038933085389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44057544219814025955390259 66086316329721038933085389)
              ·
                refine ⟨24782368623645389599907021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66086316329721038933085389 24782368623645389599907021)
                ·
                  refine ⟨9293388233867021099965133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24782368623645389599907021 9293388233867021099965133)
                  ·
                    refine ⟨3485020587700132912486925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9293388233867021099965133 3485020587700132912486925)
                    ·
                      refine ⟨1306882720387549842182597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3485020587700132912486925 1306882720387549842182597)
                      ·
                        rfl

theorem cell23_2545145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 3, 3, 3, 3].length) (baseStart_2545145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545145 prefixEnd_2545145 := by exact prefixLift 2545145
  have htrace : WordTrace (prefixWord ++ tailWord_2545145) baseStart_2545145 baseEnd_2545145 := by
    simpa [prefixWord, tailWord_2545145, baseEnd_2545145] using wordTrace_append hprefix tailTrace_2545145
  have hstable : (prefixWord ++ tailWord_2545145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545145).length < 2 ^ (prefixWord ++ tailWord_2545145).sum := by decide
  have hdescent : baseEnd_2545145 < baseStart_2545145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545163 : List Nat := [1, 1, 1, 1, 9, 1, 1, 1, 3, 2, 2]
def baseStart_2545163 : Nat := 118140960795 + 2545163 * 2 ^ 59
def prefixEnd_2545163 : Nat := 4983230072969 + 3 ^ 40 * 2545163 * 2
def baseEnd_2545163 : Nat := 1306891963039330771757515

theorem tailTrace_2545163 : CollatzResearch.WordTrace tailWord_2545163 prefixEnd_2545163 1306891963039330771757515 := by
  unfold tailWord_2545163
  simp only [CollatzResearch.WordTrace]
  refine ⟨92829720878316605078928143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61886480585544403385952095 92829720878316605078928143)
  ·
    refine ⟨139244581317474907618392215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92829720878316605078928143 139244581317474907618392215)
    ·
      refine ⟨208866871976212361427588323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139244581317474907618392215 208866871976212361427588323)
      ·
        refine ⟨313300307964318542141382485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208866871976212361427588323 313300307964318542141382485)
        ·
          refine ⟨1835743991978428957859663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 313300307964318542141382485 1835743991978428957859663)
          ·
            refine ⟨2753615987967643436789495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835743991978428957859663 2753615987967643436789495)
            ·
              refine ⟨4130423981951465155184243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753615987967643436789495 4130423981951465155184243)
              ·
                refine ⟨6195635972927197732776365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4130423981951465155184243 6195635972927197732776365)
                ·
                  refine ⟨2323363489847699149791137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6195635972927197732776365 2323363489847699149791137)
                  ·
                    refine ⟨1742522617385774362343353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2323363489847699149791137 1742522617385774362343353)
                    ·
                      refine ⟨1306891963039330771757515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742522617385774362343353 1306891963039330771757515)
                      ·
                        rfl

theorem cell23_2545163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 1, 1, 1, 3, 2, 2].length) (baseStart_2545163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545163 prefixEnd_2545163 := by exact prefixLift 2545163
  have htrace : WordTrace (prefixWord ++ tailWord_2545163) baseStart_2545163 baseEnd_2545163 := by
    simpa [prefixWord, tailWord_2545163, baseEnd_2545163] using wordTrace_append hprefix tailTrace_2545163
  have hstable : (prefixWord ++ tailWord_2545163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545163).length < 2 ^ (prefixWord ++ tailWord_2545163).sum := by decide
  have hdescent : baseEnd_2545163 < baseStart_2545163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545229 : List Nat := [1, 6, 1, 1, 3, 1, 1, 1, 2, 6]
def baseStart_2545229 : Nat := 118140960795 + 2545229 * 2 ^ 59
def prefixEnd_2545229 : Nat := 4983230072969 + 3 ^ 40 * 2545229 * 2
def baseEnd_2545229 : Nat := 435641950920842504510737

theorem tailTrace_2545229 : CollatzResearch.WordTrace tailWord_2545229 prefixEnd_2545229 435641950920842504510737 := by
  unfold tailWord_2545229
  simp only [CollatzResearch.WordTrace]
  refine ⟨92832128096077498350830741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61888085397384998900553827 92832128096077498350830741)
  ·
    refine ⟨4351506004503632735195191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92832128096077498350830741 4351506004503632735195191)
    ·
      refine ⟨6527259006755449102792787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4351506004503632735195191 6527259006755449102792787)
      ·
        refine ⟨9790888510133173654189181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6527259006755449102792787 9790888510133173654189181)
        ·
          refine ⟨3671583191299940120320943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9790888510133173654189181 3671583191299940120320943)
          ·
            refine ⟨5507374786949910180481415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3671583191299940120320943 5507374786949910180481415)
            ·
              refine ⟨8261062180424865270722123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5507374786949910180481415 8261062180424865270722123)
              ·
                refine ⟨12391593270637297906083185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8261062180424865270722123 12391593270637297906083185)
                ·
                  refine ⟨9293694952977973429562389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12391593270637297906083185 9293694952977973429562389)
                  ·
                    refine ⟨435641950920842504510737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9293694952977973429562389 435641950920842504510737)
                    ·
                      rfl

theorem cell23_2545229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 1, 2, 6].length) (baseStart_2545229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545229 prefixEnd_2545229 := by exact prefixLift 2545229
  have htrace : WordTrace (prefixWord ++ tailWord_2545229) baseStart_2545229 baseEnd_2545229 := by
    simpa [prefixWord, tailWord_2545229, baseEnd_2545229] using wordTrace_append hprefix tailTrace_2545229
  have hstable : (prefixWord ++ tailWord_2545229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545229).length < 2 ^ (prefixWord ++ tailWord_2545229).sum := by decide
  have hdescent : baseEnd_2545229 < baseStart_2545229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545236 : List Nat := [2, 4, 1, 1, 1, 2, 1, 5, 2, 2, 2]
def baseStart_2545236 : Nat := 118140960795 + 2545236 * 2 ^ 59
def prefixEnd_2545236 : Nat := 4983230072969 + 3 ^ 40 * 2545236 * 2
def baseEnd_2545236 : Nat := 1306929447127108986144679

theorem tailTrace_2545236 : CollatzResearch.WordTrace tailWord_2545236 prefixEnd_2545236 1306929447127108986144679 := by
  unfold tailWord_2545236
  simp only [CollatzResearch.WordTrace]
  refine ⟨46416191703526069273167781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61888255604701425697557041 46416191703526069273167781)
  ·
    refine ⟨8703035944411137988718959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46416191703526069273167781 8703035944411137988718959)
    ·
      refine ⟨13054553916616706983078439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8703035944411137988718959 13054553916616706983078439)
      ·
        refine ⟨19581830874925060474617659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13054553916616706983078439 19581830874925060474617659)
        ·
          refine ⟨29372746312387590711926489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19581830874925060474617659 29372746312387590711926489)
          ·
            refine ⟨22029559734290693033944867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29372746312387590711926489 22029559734290693033944867)
            ·
              refine ⟨33044339601436039550917301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22029559734290693033944867 33044339601436039550917301)
              ·
                refine ⟨3097906837634628707898497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33044339601436039550917301 3097906837634628707898497)
                ·
                  refine ⟨2323430128225971530923873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3097906837634628707898497 2323430128225971530923873)
                  ·
                    refine ⟨1742572596169478648192905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2323430128225971530923873 1742572596169478648192905)
                    ·
                      refine ⟨1306929447127108986144679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742572596169478648192905 1306929447127108986144679)
                      ·
                        rfl

theorem cell23_2545236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 1, 5, 2, 2, 2].length) (baseStart_2545236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545236 prefixEnd_2545236 := by exact prefixLift 2545236
  have htrace : WordTrace (prefixWord ++ tailWord_2545236) baseStart_2545236 baseEnd_2545236 := by
    simpa [prefixWord, tailWord_2545236, baseEnd_2545236] using wordTrace_append hprefix tailTrace_2545236
  have hstable : (prefixWord ++ tailWord_2545236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545236).length < 2 ^ (prefixWord ++ tailWord_2545236).sum := by decide
  have hdescent : baseEnd_2545236 < baseStart_2545236 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545265 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_2545265 : Nat := 118140960795 + 2545265 * 2 ^ 59
def prefixEnd_2545265 : Nat := 4983230072969 + 3 ^ 40 * 2545265 * 2
def baseEnd_2545265 : Nat := 1306944338066089372682045

theorem tailTrace_2545265 : CollatzResearch.WordTrace tailWord_2545265 prefixEnd_2545265 1306944338066089372682045 := by
  unfold tailWord_2545265
  simp only [CollatzResearch.WordTrace]
  refine ⟨92833441123947076499141249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61888960749298050999427499 92833441123947076499141249)
  ·
    refine ⟨69625080842960307374355937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92833441123947076499141249 69625080842960307374355937)
    ·
      refine ⟨52218810632220230530766953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69625080842960307374355937 52218810632220230530766953)
      ·
        refine ⟨39164107974165172898075215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52218810632220230530766953 39164107974165172898075215)
        ·
          refine ⟨58746161961247759347112823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39164107974165172898075215 58746161961247759347112823)
          ·
            refine ⟨88119242941871639020669235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58746161961247759347112823 88119242941871639020669235)
            ·
              refine ⟨132178864412807458531003853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88119242941871639020669235 132178864412807458531003853)
              ·
                refine ⟨49567074154802796949126445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132178864412807458531003853 49567074154802796949126445)
                ·
                  refine ⟨18587652808051048855922417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49567074154802796949126445 18587652808051048855922417)
                  ·
                    refine ⟨13940739606038286641941813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18587652808051048855922417 13940739606038286641941813)
                    ·
                      refine ⟨1306944338066089372682045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13940739606038286641941813 1306944338066089372682045)
                      ·
                        rfl

theorem cell23_2545265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_2545265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545265 prefixEnd_2545265 := by exact prefixLift 2545265
  have htrace : WordTrace (prefixWord ++ tailWord_2545265) baseStart_2545265 baseEnd_2545265 := by
    simpa [prefixWord, tailWord_2545265, baseEnd_2545265] using wordTrace_append hprefix tailTrace_2545265
  have hstable : (prefixWord ++ tailWord_2545265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545265).length < 2 ^ (prefixWord ++ tailWord_2545265).sum := by decide
  have hdescent : baseEnd_2545265 < baseStart_2545265 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545269 : List Nat := [1, 3, 4, 2, 1, 1, 1, 2, 2, 3, 3]
def baseStart_2545269 : Nat := 118140960795 + 2545269 * 2 ^ 59
def prefixEnd_2545269 : Nat := 4983230072969 + 3 ^ 40 * 2545269 * 2
def baseEnd_2545269 : Nat := 1306946391988707357032027

theorem tailTrace_2545269 : CollatzResearch.WordTrace tailWord_2545269 prefixEnd_2545269 1306946391988707357032027 := by
  unfold tailWord_2545269
  simp only [CollatzResearch.WordTrace]
  refine ⟨92833587015932585182286861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61889058010621723454857907 92833587015932585182286861)
  ·
    refine ⟨34812595130974719443357573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92833587015932585182286861 34812595130974719443357573)
    ·
      refine ⟨6527361587057759895629545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34812595130974719443357573 6527361587057759895629545)
      ·
        refine ⟨4895521190293319921722159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6527361587057759895629545 4895521190293319921722159)
        ·
          refine ⟨7343281785439979882583239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4895521190293319921722159 7343281785439979882583239)
          ·
            refine ⟨11014922678159969823874859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7343281785439979882583239 11014922678159969823874859)
            ·
              refine ⟨16522384017239954735812289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11014922678159969823874859 16522384017239954735812289)
              ·
                refine ⟨12391788012929966051859217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16522384017239954735812289 12391788012929966051859217)
                ·
                  refine ⟨9293841009697474538894413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12391788012929966051859217 9293841009697474538894413)
                  ·
                    refine ⟨3485190378636552952085405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9293841009697474538894413 3485190378636552952085405)
                    ·
                      refine ⟨1306946391988707357032027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3485190378636552952085405 1306946391988707357032027)
                      ·
                        rfl

theorem cell23_2545269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 1, 2, 2, 3, 3].length) (baseStart_2545269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545269 prefixEnd_2545269 := by exact prefixLift 2545269
  have htrace : WordTrace (prefixWord ++ tailWord_2545269) baseStart_2545269 baseEnd_2545269 := by
    simpa [prefixWord, tailWord_2545269, baseEnd_2545269] using wordTrace_append hprefix tailTrace_2545269
  have hstable : (prefixWord ++ tailWord_2545269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545269).length < 2 ^ (prefixWord ++ tailWord_2545269).sum := by decide
  have hdescent : baseEnd_2545269 < baseStart_2545269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545270 : List Nat := [5, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2]
def baseStart_2545270 : Nat := 118140960795 + 2545270 * 2 ^ 59
def prefixEnd_2545270 : Nat := 4983230072969 + 3 ^ 40 * 2545270 * 2
def baseEnd_2545270 : Nat := 1306946905469361853119523

theorem tailTrace_2545270 : CollatzResearch.WordTrace tailWord_2545270 prefixEnd_2545270 1306946905469361853119523 := by
  unfold tailWord_2545270
  simp only [CollatzResearch.WordTrace]
  refine ⟨5802101468058060147067079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61889082325952641568715509 5802101468058060147067079)
  ·
    refine ⟨8703152202087090220600619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5802101468058060147067079 8703152202087090220600619)
    ·
      refine ⟨13054728303130635330900929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8703152202087090220600619 13054728303130635330900929)
      ·
        refine ⟨9791046227347976498175697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13054728303130635330900929 9791046227347976498175697)
        ·
          refine ⟨7343284670510982373631773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9791046227347976498175697 7343284670510982373631773)
          ·
            refine ⟨2753731751441618390111915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7343284670510982373631773 2753731751441618390111915)
            ·
              refine ⟨4130597627162427585167873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753731751441618390111915 4130597627162427585167873)
              ·
                refine ⟨3097948220371820688875905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4130597627162427585167873 3097948220371820688875905)
                ·
                  refine ⟨2323461165278865516656929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3097948220371820688875905 2323461165278865516656929)
                  ·
                    refine ⟨1742595873959149137492697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2323461165278865516656929 1742595873959149137492697)
                    ·
                      refine ⟨1306946905469361853119523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742595873959149137492697 1306946905469361853119523)
                      ·
                        rfl

theorem cell23_2545270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2].length) (baseStart_2545270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545270 prefixEnd_2545270 := by exact prefixLift 2545270
  have htrace : WordTrace (prefixWord ++ tailWord_2545270) baseStart_2545270 baseEnd_2545270 := by
    simpa [prefixWord, tailWord_2545270, baseEnd_2545270] using wordTrace_append hprefix tailTrace_2545270
  have hstable : (prefixWord ++ tailWord_2545270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545270).length < 2 ^ (prefixWord ++ tailWord_2545270).sum := by decide
  have hdescent : baseEnd_2545270 < baseStart_2545270 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545305 : List Nat := [1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 6]
def baseStart_2545305 : Nat := 118140960795 + 2545305 * 2 ^ 59
def prefixEnd_2545305 : Nat := 4983230072969 + 3 ^ 40 * 2545305 * 2
def baseEnd_2545305 : Nat := 1306964877292269216181861

theorem tailTrace_2545305 : CollatzResearch.WordTrace tailWord_2545305 prefixEnd_2545305 1306964877292269216181861 := by
  unfold tailWord_2545305
  simp only [CollatzResearch.WordTrace]
  refine ⟨92834900043802163330597369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61889933362534775553731579 92834900043802163330597369)
  ·
    refine ⟨69626175032851622497948027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92834900043802163330597369 69626175032851622497948027)
    ·
      refine ⟨104439262549277433746922041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69626175032851622497948027 104439262549277433746922041)
      ·
        refine ⟨78329446911958075310191531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104439262549277433746922041 78329446911958075310191531)
        ·
          refine ⟨117494170367937112965287297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78329446911958075310191531 117494170367937112965287297)
          ·
            refine ⟨88120627775952834723965473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117494170367937112965287297 88120627775952834723965473)
            ·
              refine ⟨66090470831964626042974105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88120627775952834723965473 66090470831964626042974105)
              ·
                refine ⟨49567853123973469532230579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66090470831964626042974105 49567853123973469532230579)
                ·
                  refine ⟨74351779685960204298345869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49567853123973469532230579 74351779685960204298345869)
                  ·
                    refine ⟨27881917382235076611879701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 74351779685960204298345869 27881917382235076611879701)
                    ·
                      refine ⟨1306964877292269216181861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27881917382235076611879701 1306964877292269216181861)
                      ·
                        rfl

theorem cell23_2545305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 3, 6].length) (baseStart_2545305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545305 prefixEnd_2545305 := by exact prefixLift 2545305
  have htrace : WordTrace (prefixWord ++ tailWord_2545305) baseStart_2545305 baseEnd_2545305 := by
    simpa [prefixWord, tailWord_2545305, baseEnd_2545305] using wordTrace_append hprefix tailTrace_2545305
  have hstable : (prefixWord ++ tailWord_2545305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545305).length < 2 ^ (prefixWord ++ tailWord_2545305).sum := by decide
  have hdescent : baseEnd_2545305 < baseStart_2545305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545315 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 10]
def baseStart_2545315 : Nat := 118140960795 + 2545315 * 2 ^ 59
def prefixEnd_2545315 : Nat := 4983230072969 + 3 ^ 40 * 2545315 * 2
def baseEnd_2545315 : Nat := 145218890233201575228535

theorem tailTrace_2545315 : CollatzResearch.WordTrace tailWord_2545315 prefixEnd_2545315 145218890233201575228535 := by
  unfold tailWord_2545315
  simp only [CollatzResearch.WordTrace]
  refine ⟨92835264773765935038461399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61890176515843956692307599 92835264773765935038461399)
  ·
    refine ⟨139252897160648902557692099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92835264773765935038461399 139252897160648902557692099)
    ·
      refine ⟨208879345740973353836538149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139252897160648902557692099 208879345740973353836538149)
      ·
        refine ⟨39164877326432503844350903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 208879345740973353836538149 39164877326432503844350903)
        ·
          refine ⟨58747315989648755766526355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39164877326432503844350903 58747315989648755766526355)
          ·
            refine ⟨88120973984473133649789533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58747315989648755766526355 88120973984473133649789533)
            ·
              refine ⟨33045365244177425118671075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88120973984473133649789533 33045365244177425118671075)
              ·
                refine ⟨49568047866266137678006613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33045365244177425118671075 49568047866266137678006613)
                ·
                  refine ⟨145218890233201575228535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 49568047866266137678006613 145218890233201575228535)
                  ·
                    rfl

theorem cell23_2545315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 10].length) (baseStart_2545315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545315 prefixEnd_2545315 := by exact prefixLift 2545315
  have htrace : WordTrace (prefixWord ++ tailWord_2545315) baseStart_2545315 baseEnd_2545315 := by
    simpa [prefixWord, tailWord_2545315, baseEnd_2545315] using wordTrace_append hprefix tailTrace_2545315
  have hstable : (prefixWord ++ tailWord_2545315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545315).length < 2 ^ (prefixWord ++ tailWord_2545315).sum := by decide
  have hdescent : baseEnd_2545315 < baseStart_2545315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545359 : List Nat := [1, 1, 2, 1, 1, 3, 1, 6, 3, 1, 3]
def baseStart_2545359 : Nat := 118140960795 + 2545359 * 2 ^ 59
def prefixEnd_2545359 : Nat := 4983230072969 + 3 ^ 40 * 2545359 * 2
def baseEnd_2545359 : Nat := 1306992605247612004906613

theorem tailTrace_2545359 : CollatzResearch.WordTrace tailWord_2545359 prefixEnd_2545359 1306992605247612004906613 := by
  unfold tailWord_2545359
  simp only [CollatzResearch.WordTrace]
  refine ⟨92836869585606530553063131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61891246390404353702042087 92836869585606530553063131)
  ·
    refine ⟨139255304378409795829594697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92836869585606530553063131 139255304378409795829594697)
    ·
      refine ⟨104441478283807346872196023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139255304378409795829594697 104441478283807346872196023)
      ·
        refine ⟨156662217425711020308294035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104441478283807346872196023 156662217425711020308294035)
        ·
          refine ⟨234993326138566530462441053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156662217425711020308294035 234993326138566530462441053)
          ·
            refine ⟨88122497301962448923415395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234993326138566530462441053 88122497301962448923415395)
            ·
              refine ⟨132183745952943673385123093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88122497301962448923415395 132183745952943673385123093)
              ·
                refine ⟨6196113091544234689927645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132183745952943673385123093 6196113091544234689927645)
                ·
                  refine ⟨2323542409329088008722867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6196113091544234689927645 2323542409329088008722867)
                  ·
                    refine ⟨3485313613993632013084301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2323542409329088008722867 3485313613993632013084301)
                    ·
                      refine ⟨1306992605247612004906613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3485313613993632013084301 1306992605247612004906613)
                      ·
                        rfl

theorem cell23_2545359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3, 1, 3].length) (baseStart_2545359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545359 prefixEnd_2545359 := by exact prefixLift 2545359
  have htrace : WordTrace (prefixWord ++ tailWord_2545359) baseStart_2545359 baseEnd_2545359 := by
    simpa [prefixWord, tailWord_2545359, baseEnd_2545359] using wordTrace_append hprefix tailTrace_2545359
  have hstable : (prefixWord ++ tailWord_2545359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545359).length < 2 ^ (prefixWord ++ tailWord_2545359).sum := by decide
  have hdescent : baseEnd_2545359 < baseStart_2545359 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545386 : List Nat := [3, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2]
def baseStart_2545386 : Nat := 118140960795 + 2545386 * 2 ^ 59
def prefixEnd_2545386 : Nat := 4983230072969 + 3 ^ 40 * 2545386 * 2
def baseEnd_2545386 : Nat := 1307006469225283399268989

theorem tailTrace_2545386 : CollatzResearch.WordTrace tailWord_2545386 prefixEnd_2545386 1307006469225283399268989 := by
  unfold tailWord_2545386
  simp only [CollatzResearch.WordTrace]
  refine ⟨23209463589127178541074003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61891902904339142776197341 23209463589127178541074003)
  ·
    refine ⟨34814195383690767811611005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23209463589127178541074003 34814195383690767811611005)
    ·
      refine ⟨13055323268884037929354127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34814195383690767811611005 13055323268884037929354127)
      ·
        refine ⟨19582984903326056894031191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13055323268884037929354127 19582984903326056894031191)
        ·
          refine ⟨29374477354989085341046787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19582984903326056894031191 29374477354989085341046787)
          ·
            refine ⟨44061716032483628011570181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29374477354989085341046787 44061716032483628011570181)
            ·
              refine ⟨8261571756090680252169409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44061716032483628011570181 8261571756090680252169409)
              ·
                refine ⟨6196178817068010189127057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8261571756090680252169409 6196178817068010189127057)
                ·
                  refine ⟨4647134112801007641845293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6196178817068010189127057 4647134112801007641845293)
                  ·
                    refine ⟨1742675292300377865691985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4647134112801007641845293 1742675292300377865691985)
                    ·
                      refine ⟨1307006469225283399268989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742675292300377865691985 1307006469225283399268989)
                      ·
                        rfl

theorem cell23_2545386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 2, 2, 3, 2].length) (baseStart_2545386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545386 prefixEnd_2545386 := by exact prefixLift 2545386
  have htrace : WordTrace (prefixWord ++ tailWord_2545386) baseStart_2545386 baseEnd_2545386 := by
    simpa [prefixWord, tailWord_2545386, baseEnd_2545386] using wordTrace_append hprefix tailTrace_2545386
  have hstable : (prefixWord ++ tailWord_2545386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545386).length < 2 ^ (prefixWord ++ tailWord_2545386).sum := by decide
  have hdescent : baseEnd_2545386 < baseStart_2545386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545393 : List Nat := [1, 2, 2, 2, 2, 4, 1, 4, 1, 1, 3]
def baseStart_2545393 : Nat := 118140960795 + 2545393 * 2 ^ 59
def prefixEnd_2545393 : Nat := 4983230072969 + 3 ^ 40 * 2545393 * 2
def baseEnd_2545393 : Nat := 1307010063589864871881457

theorem tailTrace_2545393 : CollatzResearch.WordTrace tailWord_2545393 prefixEnd_2545393 1307010063589864871881457 := by
  unfold tailWord_2545393
  simp only [CollatzResearch.WordTrace]
  refine ⟨92838109667483354359800833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61892073111655569573200555 92838109667483354359800833)
  ·
    refine ⟨69628582250612515769850625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92838109667483354359800833 69628582250612515769850625)
    ·
      refine ⟨52221436687959386827387969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69628582250612515769850625 52221436687959386827387969)
      ·
        refine ⟨39166077515969540120540977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52221436687959386827387969 39166077515969540120540977)
        ·
          refine ⟨29374558136977155090405733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39166077515969540120540977 29374558136977155090405733)
          ·
            refine ⟨5507729650683216579451075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29374558136977155090405733 5507729650683216579451075)
            ·
              refine ⟨8261594476024824869176613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5507729650683216579451075 8261594476024824869176613)
              ·
                refine ⟨1549048964254654662970615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8261594476024824869176613 1549048964254654662970615)
                ·
                  refine ⟨2323573446381981994455923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549048964254654662970615 2323573446381981994455923)
                  ·
                    refine ⟨3485360169572972991683885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2323573446381981994455923 3485360169572972991683885)
                    ·
                      refine ⟨1307010063589864871881457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3485360169572972991683885 1307010063589864871881457)
                      ·
                        rfl

theorem cell23_2545393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_2545393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545393 prefixEnd_2545393 := by exact prefixLift 2545393
  have htrace : WordTrace (prefixWord ++ tailWord_2545393) baseStart_2545393 baseEnd_2545393 := by
    simpa [prefixWord, tailWord_2545393, baseEnd_2545393] using wordTrace_append hprefix tailTrace_2545393
  have hstable : (prefixWord ++ tailWord_2545393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545393).length < 2 ^ (prefixWord ++ tailWord_2545393).sum := by decide
  have hdescent : baseEnd_2545393 < baseStart_2545393 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545402 : List Nat := [3, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_2545402 : Nat := 118140960795 + 2545402 * 2 ^ 59
def prefixEnd_2545402 : Nat := 4983230072969 + 3 ^ 40 * 2545402 * 2
def baseEnd_2545402 : Nat := 1307014684915755336668915

theorem tailTrace_2545402 : CollatzResearch.WordTrace tailWord_2545402 prefixEnd_2545402 1307014684915755336668915 := by
  unfold tailWord_2545402
  simp only [CollatzResearch.WordTrace]
  refine ⟨23209609481112687224219615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61892291949633832597918973 23209609481112687224219615)
  ·
    refine ⟨34814414221669030836329423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23209609481112687224219615 34814414221669030836329423)
    ·
      refine ⟨52221621332503546254494135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34814414221669030836329423 52221621332503546254494135)
      ·
        refine ⟨78332431998755319381741203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52221621332503546254494135 78332431998755319381741203)
        ·
          refine ⟨117498647998132979072611805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78332431998755319381741203 117498647998132979072611805)
          ·
            refine ⟨44061992999299867152229427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117498647998132979072611805 44061992999299867152229427)
            ·
              refine ⟨66092989498949800728344141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44061992999299867152229427 66092989498949800728344141)
              ·
                refine ⟨24784871062106175273129053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66092989498949800728344141 24784871062106175273129053)
                ·
                  refine ⟨9294326648289815727423395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24784871062106175273129053 9294326648289815727423395)
                  ·
                    refine ⟨13941489972434723591135093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9294326648289815727423395 13941489972434723591135093)
                    ·
                      refine ⟨1307014684915755336668915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13941489972434723591135093 1307014684915755336668915)
                      ·
                        rfl

theorem cell23_2545402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_2545402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545402 prefixEnd_2545402 := by exact prefixLift 2545402
  have htrace : WordTrace (prefixWord ++ tailWord_2545402) baseStart_2545402 baseEnd_2545402 := by
    simpa [prefixWord, tailWord_2545402, baseEnd_2545402] using wordTrace_append hprefix tailTrace_2545402
  have hstable : (prefixWord ++ tailWord_2545402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545402).length < 2 ^ (prefixWord ++ tailWord_2545402).sum := by decide
  have hdescent : baseEnd_2545402 < baseStart_2545402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545419 : List Nat := [1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 3]
def baseStart_2545419 : Nat := 118140960795 + 2545419 * 2 ^ 59
def prefixEnd_2545419 : Nat := 4983230072969 + 3 ^ 40 * 2545419 * 2
def baseEnd_2545419 : Nat := 1307023414086881770156337

theorem tailTrace_2545419 : CollatzResearch.WordTrace tailWord_2545419 prefixEnd_2545419 1307023414086881770156337 := by
  unfold tailWord_2545419
  simp only [CollatzResearch.WordTrace]
  refine ⟨92839057965389160800247311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61892705310259440533498207 92839057965389160800247311)
  ·
    refine ⟨139258586948083741200370967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92839057965389160800247311 139258586948083741200370967)
    ·
      refine ⟨208887880422125611800556451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139258586948083741200370967 208887880422125611800556451)
      ·
        refine ⟨313331820633188417700834677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208887880422125611800556451 313331820633188417700834677)
        ·
          refine ⟨29374858184361414159453251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 313331820633188417700834677 29374858184361414159453251)
          ·
            refine ⟨44062287276542121239179877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29374858184361414159453251 44062287276542121239179877)
            ·
              refine ⟨8261678864351647732346227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44062287276542121239179877 8261678864351647732346227)
              ·
                refine ⟨12392518296527471598519341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8261678864351647732346227 12392518296527471598519341)
                ·
                  refine ⟨4647194361197801849444753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12392518296527471598519341 4647194361197801849444753)
                  ·
                    refine ⟨3485395770898351387083565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4647194361197801849444753 3485395770898351387083565)
                    ·
                      refine ⟨1307023414086881770156337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3485395770898351387083565 1307023414086881770156337)
                      ·
                        rfl

theorem cell23_2545419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 4, 1, 3, 2, 3].length) (baseStart_2545419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545419 prefixEnd_2545419 := by exact prefixLift 2545419
  have htrace : WordTrace (prefixWord ++ tailWord_2545419) baseStart_2545419 baseEnd_2545419 := by
    simpa [prefixWord, tailWord_2545419, baseEnd_2545419] using wordTrace_append hprefix tailTrace_2545419
  have hstable : (prefixWord ++ tailWord_2545419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545419).length < 2 ^ (prefixWord ++ tailWord_2545419).sum := by decide
  have hdescent : baseEnd_2545419 < baseStart_2545419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545422 : List Nat := [4, 1, 1, 2, 1, 1, 2, 11]
def baseStart_2545422 : Nat := 118140960795 + 2545422 * 2 ^ 59
def prefixEnd_2545422 : Nat := 4983230072969 + 3 ^ 40 * 2545422 * 2
def baseEnd_2545422 : Nat := 48408331649216491052549

theorem tailTrace_2545422 : CollatzResearch.WordTrace tailWord_2545422 prefixEnd_2545422 48408331649216491052549 := by
  unfold tailWord_2545422
  simp only [CollatzResearch.WordTrace]
  refine ⟨11604895923047286539075815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61892778256252194875071013 11604895923047286539075815)
  ·
    refine ⟨17407343884570929808613723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11604895923047286539075815 17407343884570929808613723)
    ·
      refine ⟨26111015826856394712920585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17407343884570929808613723 26111015826856394712920585)
      ·
        refine ⟨19583261870142296034690439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26111015826856394712920585 19583261870142296034690439)
        ·
          refine ⟨29374892805213444052035659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19583261870142296034690439 29374892805213444052035659)
          ·
            refine ⟨44062339207820166078053489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29374892805213444052035659 44062339207820166078053489)
            ·
              refine ⟨33046754405865124558540117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44062339207820166078053489 33046754405865124558540117)
              ·
                refine ⟨48408331649216491052549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 33046754405865124558540117 48408331649216491052549)
                ·
                  rfl

theorem cell23_2545422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 11].length) (baseStart_2545422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545422 prefixEnd_2545422 := by exact prefixLift 2545422
  have htrace : WordTrace (prefixWord ++ tailWord_2545422) baseStart_2545422 baseEnd_2545422 := by
    simpa [prefixWord, tailWord_2545422, baseEnd_2545422] using wordTrace_append hprefix tailTrace_2545422
  have hstable : (prefixWord ++ tailWord_2545422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545422).length < 2 ^ (prefixWord ++ tailWord_2545422).sum := by decide
  have hdescent : baseEnd_2545422 < baseStart_2545422 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545426 : List Nat := [3, 2, 4, 1, 1, 1, 2, 2, 1, 6]
def baseStart_2545426 : Nat := 118140960795 + 2545426 * 2 ^ 59
def prefixEnd_2545426 : Nat := 4983230072969 + 3 ^ 40 * 2545426 * 2
def baseEnd_2545426 : Nat := 435675669483821080922935

theorem tailTrace_2545426 : CollatzResearch.WordTrace tailWord_2545426 prefixEnd_2545426 435675669483821080922935 := by
  unfold tailWord_2545426
  simp only [CollatzResearch.WordTrace]
  refine ⟨23209828319090950248938033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61892875517575867330501421 23209828319090950248938033)
  ·
    refine ⟨17407371239318212686703525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23209828319090950248938033 17407371239318212686703525)
    ·
      refine ⟨3263882107372164878756911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17407371239318212686703525 3263882107372164878756911)
      ·
        refine ⟨4895823161058247318135367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3263882107372164878756911 4895823161058247318135367)
        ·
          refine ⟨7343734741587370977203051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4895823161058247318135367 7343734741587370977203051)
          ·
            refine ⟨11015602112381056465804577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7343734741587370977203051 11015602112381056465804577)
            ·
              refine ⟨8261701584285792349353433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11015602112381056465804577 8261701584285792349353433)
              ·
                refine ⟨6196276188214344262015075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8261701584285792349353433 6196276188214344262015075)
                ·
                  refine ⟨9294414282321516393022613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6196276188214344262015075 9294414282321516393022613)
                  ·
                    refine ⟨435675669483821080922935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9294414282321516393022613 435675669483821080922935)
                    ·
                      rfl

theorem cell23_2545426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_2545426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545426 prefixEnd_2545426 := by exact prefixLift 2545426
  have htrace : WordTrace (prefixWord ++ tailWord_2545426) baseStart_2545426 baseEnd_2545426 := by
    simpa [prefixWord, tailWord_2545426, baseEnd_2545426] using wordTrace_append hprefix tailTrace_2545426
  have hstable : (prefixWord ++ tailWord_2545426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545426).length < 2 ^ (prefixWord ++ tailWord_2545426).sum := by decide
  have hdescent : baseEnd_2545426 < baseStart_2545426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545429 : List Nat := [1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 4]
def baseStart_2545429 : Nat := 118140960795 + 2545429 * 2 ^ 59
def prefixEnd_2545429 : Nat := 4983230072969 + 3 ^ 40 * 2545429 * 2
def baseEnd_2545429 : Nat := 1307028548893426731031291

theorem tailTrace_2545429 : CollatzResearch.WordTrace tailWord_2545429 prefixEnd_2545429 1307028548893426731031291 := by
  unfold tailWord_2545429
  simp only [CollatzResearch.WordTrace]
  refine ⟨92839422695352932508111341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61892948463568621672074227 92839422695352932508111341)
  ·
    refine ⟨34814783510757349690541753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92839422695352932508111341 34814783510757349690541753)
    ·
      refine ⟨26111087633068012267906315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34814783510757349690541753 26111087633068012267906315)
      ·
        refine ⟨39166631449602018401859473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26111087633068012267906315 39166631449602018401859473)
        ·
          refine ⟨29374973587201513801394605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39166631449602018401859473 29374973587201513801394605)
          ·
            refine ⟨11015615095200567675522977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29374973587201513801394605 11015615095200567675522977)
            ·
              refine ⟨8261711321400425756642233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11015615095200567675522977 8261711321400425756642233)
              ·
                refine ⟨6196283491050319317481675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8261711321400425756642233 6196283491050319317481675)
                ·
                  refine ⟨9294425236575478976222513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6196283491050319317481675 9294425236575478976222513)
                  ·
                    refine ⟨6970818927431609232166885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9294425236575478976222513 6970818927431609232166885)
                    ·
                      refine ⟨1307028548893426731031291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6970818927431609232166885 1307028548893426731031291)
                      ·
                        rfl

theorem cell23_2545429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2, 1, 2, 4].length) (baseStart_2545429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545429 prefixEnd_2545429 := by exact prefixLift 2545429
  have htrace : WordTrace (prefixWord ++ tailWord_2545429) baseStart_2545429 baseEnd_2545429 := by
    simpa [prefixWord, tailWord_2545429, baseEnd_2545429] using wordTrace_append hprefix tailTrace_2545429
  have hstable : (prefixWord ++ tailWord_2545429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545429).length < 2 ^ (prefixWord ++ tailWord_2545429).sum := by decide
  have hdescent : baseEnd_2545429 < baseStart_2545429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545436 : List Nat := [2, 2, 3, 1, 1, 2, 3, 3, 1, 2, 3]
def baseStart_2545436 : Nat := 118140960795 + 2545436 * 2 ^ 59
def prefixEnd_2545436 : Nat := 4983230072969 + 3 ^ 40 * 2545436 * 2
def baseEnd_2545436 : Nat := 1307032143258008203643759

theorem tailTrace_2545436 : CollatzResearch.WordTrace tailWord_2545436 prefixEnd_2545436 1307032143258008203643759 := by
  unfold tailWord_2545436
  simp only [CollatzResearch.WordTrace]
  refine ⟨46419839003163786351808081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61893118670885048469077441 46419839003163786351808081)
  ·
    refine ⟨34814879252372839763856061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46419839003163786351808081 34814879252372839763856061)
    ·
      refine ⟨13055579719639814911446023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34814879252372839763856061 13055579719639814911446023)
      ·
        refine ⟨19583369579459722367169035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13055579719639814911446023 19583369579459722367169035)
        ·
          refine ⟨29375054369189583550753553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19583369579459722367169035 29375054369189583550753553)
          ·
            refine ⟨22031290776892187663065165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29375054369189583550753553 22031290776892187663065165)
            ·
              refine ⟨8261734041334570373649437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22031290776892187663065165 8261734041334570373649437)
              ·
                refine ⟨3098150265500463890118539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8261734041334570373649437 3098150265500463890118539)
                ·
                  refine ⟨4647225398250695835177809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3098150265500463890118539 4647225398250695835177809)
                  ·
                    refine ⟨3485419048688021876383357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4647225398250695835177809 3485419048688021876383357)
                    ·
                      refine ⟨1307032143258008203643759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3485419048688021876383357 1307032143258008203643759)
                      ·
                        rfl

theorem cell23_2545436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_2545436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545436 prefixEnd_2545436 := by exact prefixLift 2545436
  have htrace : WordTrace (prefixWord ++ tailWord_2545436) baseStart_2545436 baseEnd_2545436 := by
    simpa [prefixWord, tailWord_2545436, baseEnd_2545436] using wordTrace_append hprefix tailTrace_2545436
  have hstable : (prefixWord ++ tailWord_2545436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545436).length < 2 ^ (prefixWord ++ tailWord_2545436).sum := by decide
  have hdescent : baseEnd_2545436 < baseStart_2545436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545460 : List Nat := [2, 5, 1, 1, 2, 2, 3, 1, 2, 4]
def baseStart_2545460 : Nat := 118140960795 + 2545460 * 2 ^ 59
def prefixEnd_2545460 : Nat := 4983230072969 + 3 ^ 40 * 2545460 * 2
def baseEnd_2545460 : Nat := 435681488931238703247883

theorem tailTrace_2545460 : CollatzResearch.WordTrace tailWord_2545460 prefixEnd_2545460 435681488931238703247883 := by
  unfold tailWord_2545460
  simp only [CollatzResearch.WordTrace]
  refine ⟨46420276679120312401244917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61893702238827083201659889 46420276679120312401244917)
  ·
    refine ⟨4351900938667529287616711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 46420276679120312401244917 4351900938667529287616711)
    ·
      refine ⟨6527851408001293931425067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4351900938667529287616711 6527851408001293931425067)
      ·
        refine ⟨9791777112001940897137601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6527851408001293931425067 9791777112001940897137601)
        ·
          refine ⟨7343832834001455672853201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9791777112001940897137601 7343832834001455672853201)
          ·
            refine ⟨5507874625501091754639901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7343832834001455672853201 5507874625501091754639901)
            ·
              refine ⟨2065452984562909407989963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5507874625501091754639901 2065452984562909407989963)
              ·
                refine ⟨3098179476844364111984945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065452984562909407989963 3098179476844364111984945)
                ·
                  refine ⟨2323634607633273083988709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3098179476844364111984945 2323634607633273083988709)
                  ·
                    refine ⟨435681488931238703247883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2323634607633273083988709 435681488931238703247883)
                    ·
                      rfl

theorem cell23_2545460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 3, 1, 2, 4].length) (baseStart_2545460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545460 prefixEnd_2545460 := by exact prefixLift 2545460
  have htrace : WordTrace (prefixWord ++ tailWord_2545460) baseStart_2545460 baseEnd_2545460 := by
    simpa [prefixWord, tailWord_2545460, baseEnd_2545460] using wordTrace_append hprefix tailTrace_2545460
  have hstable : (prefixWord ++ tailWord_2545460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545460).length < 2 ^ (prefixWord ++ tailWord_2545460).sum := by decide
  have hdescent : baseEnd_2545460 < baseStart_2545460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545466 : List Nat := [3, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3]
def baseStart_2545466 : Nat := 118140960795 + 2545466 * 2 ^ 59
def prefixEnd_2545466 : Nat := 4983230072969 + 3 ^ 40 * 2545466 * 2
def baseEnd_2545466 : Nat := 1307047547677643086268621

theorem tailTrace_2545466 : CollatzResearch.WordTrace tailWord_2545466 prefixEnd_2545466 1307047547677643086268621 := by
  unfold tailWord_2545466
  simp only [CollatzResearch.WordTrace]
  refine ⟨23210193049054721956802063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61893848130812591884805501 23210193049054721956802063)
  ·
    refine ⟨34815289573582082935203095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23210193049054721956802063 34815289573582082935203095)
    ·
      refine ⟨52222934360373124402804643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34815289573582082935203095 52222934360373124402804643)
      ·
        refine ⟨78334401540559686604206965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52222934360373124402804643 78334401540559686604206965)
        ·
          refine ⟨7343850144427470619144403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78334401540559686604206965 7343850144427470619144403)
          ·
            refine ⟨11015775216641205928716605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7343850144427470619144403 11015775216641205928716605)
            ·
              refine ⟨4130915706240452223268727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11015775216641205928716605 4130915706240452223268727)
              ·
                refine ⟨6196373559360678334903091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4130915706240452223268727 6196373559360678334903091)
                ·
                  refine ⟨9294560339041017502354637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6196373559360678334903091 9294560339041017502354637)
                  ·
                    refine ⟨3485460127140381563382989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9294560339041017502354637 3485460127140381563382989)
                    ·
                      refine ⟨1307047547677643086268621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3485460127140381563382989 1307047547677643086268621)
                      ·
                        rfl

theorem cell23_2545466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 3, 1, 1, 3, 3].length) (baseStart_2545466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545466 prefixEnd_2545466 := by exact prefixLift 2545466
  have htrace : WordTrace (prefixWord ++ tailWord_2545466) baseStart_2545466 baseEnd_2545466 := by
    simpa [prefixWord, tailWord_2545466, baseEnd_2545466] using wordTrace_append hprefix tailTrace_2545466
  have hstable : (prefixWord ++ tailWord_2545466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545466).length < 2 ^ (prefixWord ++ tailWord_2545466).sum := by decide
  have hdescent : baseEnd_2545466 < baseStart_2545466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545484 : List Nat := [2, 2, 1, 3, 5, 1, 1, 3, 1, 2, 2]
def baseStart_2545484 : Nat := 118140960795 + 2545484 * 2 ^ 59
def prefixEnd_2545484 : Nat := 4983230072969 + 3 ^ 40 * 2545484 * 2
def baseEnd_2545484 : Nat := 1307056790329424015843539

theorem tailTrace_2545484 : CollatzResearch.WordTrace tailWord_2545484 prefixEnd_2545484 1307056790329424015843539 := by
  unfold tailWord_2545484
  simp only [CollatzResearch.WordTrace]
  refine ⟨46420714355076838450681753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61894285806769117934242337 46420714355076838450681753)
  ·
    refine ⟨34815535766307628838011315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46420714355076838450681753 34815535766307628838011315)
    ·
      refine ⟨52223303649461443257016973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34815535766307628838011315 52223303649461443257016973)
      ·
        refine ⟨19583738868548041221381365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52223303649461443257016973 19583738868548041221381365)
        ·
          refine ⟨1835975518926378864504503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19583738868548041221381365 1835975518926378864504503)
          ·
            refine ⟨2753963278389568296756755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1835975518926378864504503 2753963278389568296756755)
            ·
              refine ⟨4130944917584352445135133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2753963278389568296756755 4130944917584352445135133)
              ·
                refine ⟨1549104344094132166925675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4130944917584352445135133 1549104344094132166925675)
                ·
                  refine ⟨2323656516141198250388513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549104344094132166925675 2323656516141198250388513)
                  ·
                    refine ⟨1742742387105898687791385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2323656516141198250388513 1742742387105898687791385)
                    ·
                      refine ⟨1307056790329424015843539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742742387105898687791385 1307056790329424015843539)
                      ·
                        rfl

theorem cell23_2545484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_2545484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545484 prefixEnd_2545484 := by exact prefixLift 2545484
  have htrace : WordTrace (prefixWord ++ tailWord_2545484) baseStart_2545484 baseEnd_2545484 := by
    simpa [prefixWord, tailWord_2545484, baseEnd_2545484] using wordTrace_append hprefix tailTrace_2545484
  have hstable : (prefixWord ++ tailWord_2545484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545484).length < 2 ^ (prefixWord ++ tailWord_2545484).sum := by decide
  have hdescent : baseEnd_2545484 < baseStart_2545484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545493 : List Nat := [1, 3, 2, 2, 2, 2, 2, 3, 1, 3, 2]
def baseStart_2545493 : Nat := 118140960795 + 2545493 * 2 ^ 59
def prefixEnd_2545493 : Nat := 4983230072969 + 3 ^ 40 * 2545493 * 2
def baseEnd_2545493 : Nat := 1307061411655314480630997

theorem tailTrace_2545493 : CollatzResearch.WordTrace tailWord_2545493 prefixEnd_2545493 1307061411655314480630997 := by
  unfold tailWord_2545493
  simp only [CollatzResearch.WordTrace]
  refine ⟨92841756967121071438441133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61894504644747380958960755 92841756967121071438441133)
  ·
    refine ⟨34815658862670401789415425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92841756967121071438441133 34815658862670401789415425)
    ·
      refine ⟨26111744147002801342061569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34815658862670401789415425 26111744147002801342061569)
      ·
        refine ⟨19583808110252101006546177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26111744147002801342061569 19583808110252101006546177)
        ·
          refine ⟨14687856082689075754909633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19583808110252101006546177 14687856082689075754909633)
          ·
            refine ⟨11015892062016806816182225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14687856082689075754909633 11015892062016806816182225)
            ·
              refine ⟨8261919046512605112136669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11015892062016806816182225 8261919046512605112136669)
              ·
                refine ⟨3098219642442226917051251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8261919046512605112136669 3098219642442226917051251)
                ·
                  refine ⟨4647329463663340375576877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3098219642442226917051251 4647329463663340375576877)
                  ·
                    refine ⟨1742748548873752640841329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4647329463663340375576877 1742748548873752640841329)
                    ·
                      refine ⟨1307061411655314480630997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742748548873752640841329 1307061411655314480630997)
                      ·
                        rfl

theorem cell23_2545493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 3, 1, 3, 2].length) (baseStart_2545493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545493 prefixEnd_2545493 := by exact prefixLift 2545493
  have htrace : WordTrace (prefixWord ++ tailWord_2545493) baseStart_2545493 baseEnd_2545493 := by
    simpa [prefixWord, tailWord_2545493, baseEnd_2545493] using wordTrace_append hprefix tailTrace_2545493
  have hstable : (prefixWord ++ tailWord_2545493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545493).length < 2 ^ (prefixWord ++ tailWord_2545493).sum := by decide
  have hdescent : baseEnd_2545493 < baseStart_2545493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545509 : List Nat := [1, 3, 1, 3, 1, 1, 1, 3, 2, 4, 3]
def baseStart_2545509 : Nat := 118140960795 + 2545509 * 2 ^ 59
def prefixEnd_2545509 : Nat := 4983230072969 + 3 ^ 40 * 2545509 * 2
def baseEnd_2545509 : Nat := 1307069627345786418030923

theorem tailTrace_2545509 : CollatzResearch.WordTrace tailWord_2545509 prefixEnd_2545509 1307069627345786418030923 := by
  unfold tailWord_2545509
  simp only [CollatzResearch.WordTrace]
  refine ⟨92842340535063106171023581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61894893690042070780682387 92842340535063106171023581)
  ·
    refine ⟨34815877700648664814133843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92842340535063106171023581 34815877700648664814133843)
    ·
      refine ⟨52223816550972997221200765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34815877700648664814133843 52223816550972997221200765)
      ·
        refine ⟨19583931206614873957950287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52223816550972997221200765 19583931206614873957950287)
        ·
          refine ⟨29375896809922310936925431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19583931206614873957950287 29375896809922310936925431)
          ·
            refine ⟨44063845214883466405388147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29375896809922310936925431 44063845214883466405388147)
            ·
              refine ⟨66095767822325199608082221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44063845214883466405388147 66095767822325199608082221)
              ·
                refine ⟨24785912933371949853030833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66095767822325199608082221 24785912933371949853030833)
                ·
                  refine ⟨18589434700028962389773125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24785912933371949853030833 18589434700028962389773125)
                  ·
                    refine ⟨3485519006255430448082461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18589434700028962389773125 3485519006255430448082461)
                    ·
                      refine ⟨1307069627345786418030923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3485519006255430448082461 1307069627345786418030923)
                      ·
                        rfl

theorem cell23_2545509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 2, 4, 3].length) (baseStart_2545509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545509 prefixEnd_2545509 := by exact prefixLift 2545509
  have htrace : WordTrace (prefixWord ++ tailWord_2545509) baseStart_2545509 baseEnd_2545509 := by
    simpa [prefixWord, tailWord_2545509, baseEnd_2545509] using wordTrace_append hprefix tailTrace_2545509
  have hstable : (prefixWord ++ tailWord_2545509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545509).length < 2 ^ (prefixWord ++ tailWord_2545509).sum := by decide
  have hdescent : baseEnd_2545509 < baseStart_2545509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545616 : List Nat := [2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 3]
def baseStart_2545616 : Nat := 118140960795 + 2545616 * 2 ^ 59
def prefixEnd_2545616 : Nat := 4983230072969 + 3 ^ 40 * 2545616 * 2
def baseEnd_2545616 : Nat := 1307124569775817499392931

theorem tailTrace_2545616 : CollatzResearch.WordTrace tailWord_2545616 prefixEnd_2545616 1307124569775817499392931 := by
  unfold tailWord_2545616
  simp only [CollatzResearch.WordTrace]
  refine ⟨46423121572837731722584351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61897495430450308963445801 46423121572837731722584351)
  ·
    refine ⟨69634682359256597583876527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46423121572837731722584351 69634682359256597583876527)
    ·
      refine ⟨104452023538884896375814791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69634682359256597583876527 104452023538884896375814791)
      ·
        refine ⟨156678035308327344563722187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104452023538884896375814791 156678035308327344563722187)
        ·
          refine ⟨235017052962491016845583281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156678035308327344563722187 235017052962491016845583281)
          ·
            refine ⟨176262789721868262634187461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235017052962491016845583281 176262789721868262634187461)
            ·
              refine ⟨33049273072850299243910149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 176262789721868262634187461 33049273072850299243910149)
              ·
                refine ⟨6196738701159431108233153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33049273072850299243910149 6196738701159431108233153)
                ·
                  refine ⟨4647554025869573331174865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6196738701159431108233153 4647554025869573331174865)
                  ·
                    refine ⟨3485665519402179998381149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4647554025869573331174865 3485665519402179998381149)
                    ·
                      refine ⟨1307124569775817499392931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3485665519402179998381149 1307124569775817499392931)
                      ·
                        rfl

theorem cell23_2545616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 3].length) (baseStart_2545616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545616 prefixEnd_2545616 := by exact prefixLift 2545616
  have htrace : WordTrace (prefixWord ++ tailWord_2545616) baseStart_2545616 baseEnd_2545616 := by
    simpa [prefixWord, tailWord_2545616, baseEnd_2545616] using wordTrace_append hprefix tailTrace_2545616
  have hstable : (prefixWord ++ tailWord_2545616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545616).length < 2 ^ (prefixWord ++ tailWord_2545616).sum := by decide
  have hdescent : baseEnd_2545616 < baseStart_2545616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545623 : List Nat := [1, 1, 3, 2, 1, 1, 3, 6, 1, 4]
def baseStart_2545623 : Nat := 118140960795 + 2545623 * 2 ^ 59
def prefixEnd_2545623 : Nat := 4983230072969 + 3 ^ 40 * 2545623 * 2
def baseEnd_2545623 : Nat := 435709388046799657335133

theorem tailTrace_2545623 : CollatzResearch.WordTrace tailWord_2545623 prefixEnd_2545623 435709388046799657335133 := by
  unfold tailWord_2545623
  simp only [CollatzResearch.WordTrace]
  refine ⟨92846498456650103640673523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61897665637766735760449015 92846498456650103640673523)
  ·
    refine ⟨139269747684975155461010285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92846498456650103640673523 139269747684975155461010285)
    ·
      refine ⟨52226155381865683297878857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139269747684975155461010285 52226155381865683297878857)
      ·
        refine ⟨39169616536399262473409143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52226155381865683297878857 39169616536399262473409143)
        ·
          refine ⟨58754424804598893710113715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39169616536399262473409143 58754424804598893710113715)
          ·
            refine ⟨88131637206898340565170573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58754424804598893710113715 88131637206898340565170573)
            ·
              refine ⟨33049363952586877711938965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88131637206898340565170573 33049363952586877711938965)
              ·
                refine ⟨1549188935277509892747139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33049363952586877711938965 1549188935277509892747139)
                ·
                  refine ⟨2323783402916264839120709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549188935277509892747139 2323783402916264839120709)
                  ·
                    refine ⟨435709388046799657335133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2323783402916264839120709 435709388046799657335133)
                    ·
                      rfl

theorem cell23_2545623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 6, 1, 4].length) (baseStart_2545623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545623 prefixEnd_2545623 := by exact prefixLift 2545623
  have htrace : WordTrace (prefixWord ++ tailWord_2545623) baseStart_2545623 baseEnd_2545623 := by
    simpa [prefixWord, tailWord_2545623, baseEnd_2545623] using wordTrace_append hprefix tailTrace_2545623
  have hstable : (prefixWord ++ tailWord_2545623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545623).length < 2 ^ (prefixWord ++ tailWord_2545623).sum := by decide
  have hdescent : baseEnd_2545623 < baseStart_2545623 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545687 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 6]
def baseStart_2545687 : Nat := 118140960795 + 2545687 * 2 ^ 59
def prefixEnd_2545687 : Nat := 4983230072969 + 3 ^ 40 * 2545687 * 2
def baseEnd_2545687 : Nat := 145240114100254080178345

theorem tailTrace_2545687 : CollatzResearch.WordTrace tailWord_2545687 prefixEnd_2545687 145240114100254080178345 := by
  unfold tailWord_2545687
  simp only [CollatzResearch.WordTrace]
  refine ⟨92848832728418242571003315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61899221818945495047335543 92848832728418242571003315)
  ·
    refine ⟨139273249092627363856504973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92848832728418242571003315 139273249092627363856504973)
    ·
      refine ⟨52227468409735261446189365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139273249092627363856504973 52227468409735261446189365)
      ·
        refine ⟨4896325163412680760580253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 52227468409735261446189365 4896325163412680760580253)
        ·
          refine ⟨1836121936279755285217595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4896325163412680760580253 1836121936279755285217595)
          ·
            refine ⟨2754182904419632927826393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836121936279755285217595 2754182904419632927826393)
            ·
              refine ⟨2065637178314724695869795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2754182904419632927826393 2065637178314724695869795)
              ·
                refine ⟨3098455767472087043804693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065637178314724695869795 3098455767472087043804693)
                ·
                  refine ⟨145240114100254080178345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3098455767472087043804693 145240114100254080178345)
                  ·
                    rfl

theorem cell23_2545687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 6].length) (baseStart_2545687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545687 prefixEnd_2545687 := by exact prefixLift 2545687
  have htrace : WordTrace (prefixWord ++ tailWord_2545687) baseStart_2545687 baseEnd_2545687 := by
    simpa [prefixWord, tailWord_2545687, baseEnd_2545687] using wordTrace_append hprefix tailTrace_2545687
  have hstable : (prefixWord ++ tailWord_2545687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545687).length < 2 ^ (prefixWord ++ tailWord_2545687).sum := by decide
  have hdescent : baseEnd_2545687 < baseStart_2545687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545726 : List Nat := [4, 2, 1, 3, 13]
def baseStart_2545726 : Nat := 118140960795 + 2545726 * 2 ^ 59
def prefixEnd_2545726 : Nat := 4983230072969 + 3 ^ 40 * 2545726 * 2
def baseEnd_2545726 : Nat := 1793115298556669504825

theorem tailTrace_2545726 : CollatzResearch.WordTrace tailWord_2545726 prefixEnd_2545726 1793115298556669504825 := by
  unfold tailWord_2545726
  simp only [CollatzResearch.WordTrace]
  refine ⟨11606281896909619028959129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61900170116851301487782021 11606281896909619028959129)
  ·
    refine ⟨8704711422682214271719347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11606281896909619028959129 8704711422682214271719347)
    ·
      refine ⟨13057067134023321407579021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8704711422682214271719347 13057067134023321407579021)
      ·
        refine ⟨4896400175258745527842133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13057067134023321407579021 4896400175258745527842133)
        ·
          refine ⟨1793115298556669504825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 4896400175258745527842133 1793115298556669504825)
          ·
            rfl

theorem cell23_2545726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 13].length) (baseStart_2545726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545726 prefixEnd_2545726 := by exact prefixLift 2545726
  have htrace : WordTrace (prefixWord ++ tailWord_2545726) baseStart_2545726 baseEnd_2545726 := by
    simpa [prefixWord, tailWord_2545726, baseEnd_2545726] using wordTrace_append hprefix tailTrace_2545726
  have hstable : (prefixWord ++ tailWord_2545726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545726).length < 2 ^ (prefixWord ++ tailWord_2545726).sum := by decide
  have hdescent : baseEnd_2545726 < baseStart_2545726 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545737 : List Nat := [1, 2, 1, 1, 2, 2, 5, 4, 1, 2, 2]
def baseStart_2545737 : Nat := 118140960795 + 2545737 * 2 ^ 59
def prefixEnd_2545737 : Nat := 4983230072969 + 3 ^ 40 * 2545737 * 2
def baseEnd_2545737 : Nat := 1307186700935011525979875

theorem tailTrace_2545737 : CollatzResearch.WordTrace tailWord_2545737 prefixEnd_2545737 1307186700935011525979875 := by
  unfold tailWord_2545737
  simp only [CollatzResearch.WordTrace]
  refine ⟨92850656378237101110323465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61900437585491400740215643 92850656378237101110323465)
  ·
    refine ⟨69637992283677825832742599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92850656378237101110323465 69637992283677825832742599)
    ·
      refine ⟨104456988425516738749113899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69637992283677825832742599 104456988425516738749113899)
      ·
        refine ⟨156685482638275108123670849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104456988425516738749113899 156685482638275108123670849)
        ·
          refine ⟨117514111978706331092753137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156685482638275108123670849 117514111978706331092753137)
          ·
            refine ⟨88135583984029748319564853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117514111978706331092753137 88135583984029748319564853)
            ·
              refine ⟨8262710998502788904959205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88135583984029748319564853 8262710998502788904959205)
              ·
                refine ⟨1549258312219272919679851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8262710998502788904959205 1549258312219272919679851)
                ·
                  refine ⟨2323887468328909379519777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549258312219272919679851 2323887468328909379519777)
                  ·
                    refine ⟨1742915601246682034639833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2323887468328909379519777 1742915601246682034639833)
                    ·
                      refine ⟨1307186700935011525979875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742915601246682034639833 1307186700935011525979875)
                      ·
                        rfl

theorem cell23_2545737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 4, 1, 2, 2].length) (baseStart_2545737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545737 prefixEnd_2545737 := by exact prefixLift 2545737
  have htrace : WordTrace (prefixWord ++ tailWord_2545737) baseStart_2545737 baseEnd_2545737 := by
    simpa [prefixWord, tailWord_2545737, baseEnd_2545737] using wordTrace_append hprefix tailTrace_2545737
  have hstable : (prefixWord ++ tailWord_2545737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545737).length < 2 ^ (prefixWord ++ tailWord_2545737).sum := by decide
  have hdescent : baseEnd_2545737 < baseStart_2545737 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545753 : List Nat := [1, 2, 1, 2, 2, 1, 6, 1, 1, 3, 3]
def baseStart_2545753 : Nat := 118140960795 + 2545753 * 2 ^ 59
def prefixEnd_2545753 : Nat := 4983230072969 + 3 ^ 40 * 2545753 * 2
def baseEnd_2545753 : Nat := 1307194916625483463379801

theorem tailTrace_2545753 : CollatzResearch.WordTrace tailWord_2545753 prefixEnd_2545753 1307194916625483463379801 := by
  unfold tailWord_2545753
  simp only [CollatzResearch.WordTrace]
  refine ⟨92851239946179135842905913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61900826630786090561937275 92851239946179135842905913)
  ·
    refine ⟨69638429959634351882179435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92851239946179135842905913 69638429959634351882179435)
    ·
      refine ⟨104457644939451527823269153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69638429959634351882179435 104457644939451527823269153)
      ·
        refine ⟨78343233704588645867451865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104457644939451527823269153 78343233704588645867451865)
        ·
          refine ⟨58757425278441484400588899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78343233704588645867451865 58757425278441484400588899)
          ·
            refine ⟨88136137917662226600883349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58757425278441484400588899 88136137917662226600883349)
            ·
              refine ⟨4131381464890416871916407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 88136137917662226600883349 4131381464890416871916407)
              ·
                refine ⟨6197072197335625307874611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131381464890416871916407 6197072197335625307874611)
                ·
                  refine ⟨9295608296003437961811917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6197072197335625307874611 9295608296003437961811917)
                  ·
                    refine ⟨3485853111001289235679469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9295608296003437961811917 3485853111001289235679469)
                    ·
                      refine ⟨1307194916625483463379801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3485853111001289235679469 1307194916625483463379801)
                      ·
                        rfl

theorem cell23_2545753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 6, 1, 1, 3, 3].length) (baseStart_2545753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545753 prefixEnd_2545753 := by exact prefixLift 2545753
  have htrace : WordTrace (prefixWord ++ tailWord_2545753) baseStart_2545753 baseEnd_2545753 := by
    simpa [prefixWord, tailWord_2545753, baseEnd_2545753] using wordTrace_append hprefix tailTrace_2545753
  have hstable : (prefixWord ++ tailWord_2545753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545753).length < 2 ^ (prefixWord ++ tailWord_2545753).sum := by decide
  have hdescent : baseEnd_2545753 < baseStart_2545753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545758 : List Nat := [4, 4, 1, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_2545758 : Nat := 118140960795 + 2545758 * 2 ^ 59
def prefixEnd_2545758 : Nat := 4983230072969 + 3 ^ 40 * 2545758 * 2
def baseEnd_2545758 : Nat := 1307197484028755943817279

theorem tailTrace_2545758 : CollatzResearch.WordTrace tailWord_2545758 prefixEnd_2545758 1307197484028755943817279 := by
  unfold tailWord_2545758
  simp only [CollatzResearch.WordTrace]
  refine ⟨11606427788895127712104741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61900948207440681131225285 11606427788895127712104741)
  ·
    refine ⟨2176205210417836446019639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11606427788895127712104741 2176205210417836446019639)
    ·
      refine ⟨3264307815626754669029459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176205210417836446019639 3264307815626754669029459)
      ·
        refine ⟨4896461723440132003544189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3264307815626754669029459 4896461723440132003544189)
        ·
          refine ⟨1836173146290049501329071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4896461723440132003544189 1836173146290049501329071)
          ·
            refine ⟨2754259719435074251993607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836173146290049501329071 2754259719435074251993607)
            ·
              refine ⟨4131389579152611377990411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754259719435074251993607 4131389579152611377990411)
              ·
                refine ⟨6197084368728917066985617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131389579152611377990411 6197084368728917066985617)
                ·
                  refine ⟨4647813276546687800239213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6197084368728917066985617 4647813276546687800239213)
                  ·
                    refine ⟨1742929978705007925089705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4647813276546687800239213 1742929978705007925089705)
                    ·
                      refine ⟨1307197484028755943817279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1742929978705007925089705 1307197484028755943817279)
                      ·
                        rfl

theorem cell23_2545758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_2545758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545758 prefixEnd_2545758 := by exact prefixLift 2545758
  have htrace : WordTrace (prefixWord ++ tailWord_2545758) baseStart_2545758 baseEnd_2545758 := by
    simpa [prefixWord, tailWord_2545758, baseEnd_2545758] using wordTrace_append hprefix tailTrace_2545758
  have hstable : (prefixWord ++ tailWord_2545758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545758).length < 2 ^ (prefixWord ++ tailWord_2545758).sum := by decide
  have hdescent : baseEnd_2545758 < baseStart_2545758 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545880 : List Nat := [2, 1, 2, 2, 4, 2, 2, 1, 2, 5]
def baseStart_2545880 : Nat := 118140960795 + 2545880 * 2 ^ 59
def prefixEnd_2545880 : Nat := 4983230072969 + 3 ^ 40 * 2545880 * 2
def baseEnd_2545880 : Nat := 435753376222868155497239

theorem tailTrace_2545880 : CollatzResearch.WordTrace tailWord_2545880 prefixEnd_2545880 435753376222868155497239 := by
  unfold tailWord_2545880
  simp only [CollatzResearch.WordTrace]
  refine ⟨46427936008359518266389547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61903914677812691021852729 46427936008359518266389547)
  ·
    refine ⟨69641904012539277399584321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46427936008359518266389547 69641904012539277399584321)
    ·
      refine ⟨52231428009404458049688241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69641904012539277399584321 52231428009404458049688241)
      ·
        refine ⟨39173571007053343537266181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52231428009404458049688241 39173571007053343537266181)
        ·
          refine ⟨7345044563822501913237409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39173571007053343537266181 7345044563822501913237409)
          ·
            refine ⟨5508783422866876434928057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7345044563822501913237409 5508783422866876434928057)
            ·
              refine ⟨4131587567150157326196043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5508783422866876434928057 4131587567150157326196043)
              ·
                refine ⟨6197381350725235989294065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131587567150157326196043 6197381350725235989294065)
                ·
                  refine ⟨4648036013043926991970549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6197381350725235989294065 4648036013043926991970549)
                  ·
                    refine ⟨435753376222868155497239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4648036013043926991970549 435753376222868155497239)
                    ·
                      rfl

theorem cell23_2545880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 2, 1, 2, 5].length) (baseStart_2545880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545880 prefixEnd_2545880 := by exact prefixLift 2545880
  have htrace : WordTrace (prefixWord ++ tailWord_2545880) baseStart_2545880 baseEnd_2545880 := by
    simpa [prefixWord, tailWord_2545880, baseEnd_2545880] using wordTrace_append hprefix tailTrace_2545880
  have hstable : (prefixWord ++ tailWord_2545880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545880).length < 2 ^ (prefixWord ++ tailWord_2545880).sum := by decide
  have hdescent : baseEnd_2545880 < baseStart_2545880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545883 : List Nat := [1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 4]
def baseStart_2545883 : Nat := 118140960795 + 2545883 * 2 ^ 59
def prefixEnd_2545883 : Nat := 4983230072969 + 3 ^ 40 * 2545883 * 2
def baseEnd_2545883 : Nat := 1307261669110567954754203

theorem tailTrace_2545883 : CollatzResearch.WordTrace tailWord_2545883 prefixEnd_2545883 1307261669110567954754203 := by
  unfold tailWord_2545883
  simp only [CollatzResearch.WordTrace]
  refine ⟨92855981435708168045138303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61903987623805445363425535 92855981435708168045138303)
  ·
    refine ⟨139283972153562252067707455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92855981435708168045138303 139283972153562252067707455)
    ·
      refine ⟨208925958230343378101561183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139283972153562252067707455 208925958230343378101561183)
      ·
        refine ⟨313388937345515067152341775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208925958230343378101561183 313388937345515067152341775)
        ·
          refine ⟨470083406018272600728512663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313388937345515067152341775 470083406018272600728512663)
          ·
            refine ⟨705125109027408901092768995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470083406018272600728512663 705125109027408901092768995)
            ·
              refine ⟨1057687663541113351639153493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 705125109027408901092768995 1057687663541113351639153493)
              ·
                refine ⟨6197388653561211044760665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1057687663541113351639153493 6197388653561211044760665)
                ·
                  refine ⟨4648041490170908283570499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6197388653561211044760665 4648041490170908283570499)
                  ·
                    refine ⟨6972062235256362425355749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4648041490170908283570499 6972062235256362425355749)
                    ·
                      refine ⟨1307261669110567954754203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6972062235256362425355749 1307261669110567954754203)
                      ·
                        rfl

theorem cell23_2545883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 4].length) (baseStart_2545883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545883 prefixEnd_2545883 := by exact prefixLift 2545883
  have htrace : WordTrace (prefixWord ++ tailWord_2545883) baseStart_2545883 baseEnd_2545883 := by
    simpa [prefixWord, tailWord_2545883, baseEnd_2545883] using wordTrace_append hprefix tailTrace_2545883
  have hstable : (prefixWord ++ tailWord_2545883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545883).length < 2 ^ (prefixWord ++ tailWord_2545883).sum := by decide
  have hdescent : baseEnd_2545883 < baseStart_2545883 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545900 : List Nat := [2, 2, 1, 1, 2, 3, 2, 2, 2, 4, 2]
def baseStart_2545900 : Nat := 118140960795 + 2545900 * 2 ^ 59
def prefixEnd_2545900 : Nat := 4983230072969 + 3 ^ 40 * 2545900 * 2
def baseEnd_2545900 : Nat := 1307270398281694388241625

theorem tailTrace_2545900 : CollatzResearch.WordTrace tailWord_2545900 prefixEnd_2545900 1307270398281694388241625 := by
  unfold tailWord_2545900
  simp only [CollatzResearch.WordTrace]
  refine ⟨46428300738323289974253577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61904400984431053299004769 46428300738323289974253577)
  ·
    refine ⟨34821225553742467480690183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46428300738323289974253577 34821225553742467480690183)
    ·
      refine ⟨52231838330613701221035275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34821225553742467480690183 52231838330613701221035275)
      ·
        refine ⟨78347757495920551831552913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52231838330613701221035275 78347757495920551831552913)
        ·
          refine ⟨58760818121940413873664685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78347757495920551831552913 58760818121940413873664685)
          ·
            refine ⟨22035306795727655202624257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58760818121940413873664685 22035306795727655202624257)
            ·
              refine ⟨16526480096795741401968193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22035306795727655202624257 16526480096795741401968193)
              ·
                refine ⟨12394860072596806051476145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16526480096795741401968193 12394860072596806051476145)
                ·
                  refine ⟨9296145054447604538607109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12394860072596806051476145 9296145054447604538607109)
                  ·
                    refine ⟨1743027197708925850988833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9296145054447604538607109 1743027197708925850988833)
                    ·
                      refine ⟨1307270398281694388241625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1743027197708925850988833 1307270398281694388241625)
                      ·
                        rfl

theorem cell23_2545900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 4, 2].length) (baseStart_2545900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545900 prefixEnd_2545900 := by exact prefixLift 2545900
  have htrace : WordTrace (prefixWord ++ tailWord_2545900) baseStart_2545900 baseEnd_2545900 := by
    simpa [prefixWord, tailWord_2545900, baseEnd_2545900] using wordTrace_append hprefix tailTrace_2545900
  have hstable : (prefixWord ++ tailWord_2545900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545900).length < 2 ^ (prefixWord ++ tailWord_2545900).sum := by decide
  have hdescent : baseEnd_2545900 < baseStart_2545900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545901 : List Nat := [1, 5, 1, 2, 4, 1, 2, 2, 5]
def baseStart_2545901 : Nat := 118140960795 + 2545901 * 2 ^ 59
def prefixEnd_2545901 : Nat := 4983230072969 + 3 ^ 40 * 2545901 * 2
def baseEnd_2545901 : Nat := 145252323529149876036569

theorem tailTrace_2545901 : CollatzResearch.WordTrace tailWord_2545901 prefixEnd_2545901 145252323529149876036569 := by
  unfold tailWord_2545901
  simp only [CollatzResearch.WordTrace]
  refine ⟨92856637949642957119293557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61904425299761971412862371 92856637949642957119293557)
  ·
    refine ⟨8705309807779027229933771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92856637949642957119293557 8705309807779027229933771)
    ·
      refine ⟨13057964711668540844900657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8705309807779027229933771 13057964711668540844900657)
      ·
        refine ⟨9793473533751405633675493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13057964711668540844900657 9793473533751405633675493)
        ·
          refine ⟨1836276287578388556314155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9793473533751405633675493 1836276287578388556314155)
          ·
            refine ⟨2754414431367582834471233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836276287578388556314155 2754414431367582834471233)
            ·
              refine ⟨2065810823525687125853425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2754414431367582834471233 2065810823525687125853425)
              ·
                refine ⟨1549358117644265344390069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2065810823525687125853425 1549358117644265344390069)
                ·
                  refine ⟨145252323529149876036569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1549358117644265344390069 145252323529149876036569)
                  ·
                    rfl

theorem cell23_2545901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_2545901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545901 prefixEnd_2545901 := by exact prefixLift 2545901
  have htrace : WordTrace (prefixWord ++ tailWord_2545901) baseStart_2545901 baseEnd_2545901 := by
    simpa [prefixWord, tailWord_2545901, baseEnd_2545901] using wordTrace_append hprefix tailTrace_2545901
  have hstable : (prefixWord ++ tailWord_2545901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545901).length < 2 ^ (prefixWord ++ tailWord_2545901).sum := by decide
  have hdescent : baseEnd_2545901 < baseStart_2545901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545923 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 6]
def baseStart_2545923 : Nat := 118140960795 + 2545923 * 2 ^ 59
def prefixEnd_2545923 : Nat := 4983230072969 + 3 ^ 40 * 2545923 * 2
def baseEnd_2545923 : Nat := 145253578704083088694891

theorem tailTrace_2545923 : CollatzResearch.WordTrace tailWord_2545923 prefixEnd_2545923 145253578704083088694891 := by
  unfold tailWord_2545923
  simp only [CollatzResearch.WordTrace]
  refine ⟨92857440355563254876594423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61904960237042169917729615 92857440355563254876594423)
  ·
    refine ⟨139286160533344882314891635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92857440355563254876594423 139286160533344882314891635)
    ·
      refine ⟨208929240800017323472337453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139286160533344882314891635 208929240800017323472337453)
      ·
        refine ⟨78348465300006496302126545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208929240800017323472337453 78348465300006496302126545)
        ·
          refine ⟨58761348975004872226594909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78348465300006496302126545 58761348975004872226594909)
          ·
            refine ⟨22035505865626827084973091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58761348975004872226594909 22035505865626827084973091)
            ·
              refine ⟨33053258798440240627459637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22035505865626827084973091 33053258798440240627459637)
              ·
                refine ⟨3098743012353772558824341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33053258798440240627459637 3098743012353772558824341)
                ·
                  refine ⟨145253578704083088694891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3098743012353772558824341 145253578704083088694891)
                  ·
                    rfl

theorem cell23_2545923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 6].length) (baseStart_2545923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545923 prefixEnd_2545923 := by exact prefixLift 2545923
  have htrace : WordTrace (prefixWord ++ tailWord_2545923) baseStart_2545923 baseEnd_2545923 := by
    simpa [prefixWord, tailWord_2545923, baseEnd_2545923] using wordTrace_append hprefix tailTrace_2545923
  have hstable : (prefixWord ++ tailWord_2545923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545923).length < 2 ^ (prefixWord ++ tailWord_2545923).sum := by decide
  have hdescent : baseEnd_2545923 < baseStart_2545923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545937 : List Nat := [1, 2, 2, 1, 1, 7, 1, 1, 2, 2, 3]
def baseStart_2545937 : Nat := 118140960795 + 2545937 * 2 ^ 59
def prefixEnd_2545937 : Nat := 4983230072969 + 3 ^ 40 * 2545937 * 2
def baseEnd_2545937 : Nat := 1307289397065910743478955

theorem tailTrace_2545937 : CollatzResearch.WordTrace tailWord_2545937 prefixEnd_2545937 1307289397065910743478955 := by
  unfold tailWord_2545937
  simp only [CollatzResearch.WordTrace]
  refine ⟨92857950977512535267604065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61905300651675023511736043 92857950977512535267604065)
  ·
    refine ⟨69643463233134401450703049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92857950977512535267604065 69643463233134401450703049)
    ·
      refine ⟨52232597424850801088027287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69643463233134401450703049 52232597424850801088027287)
      ·
        refine ⟨78348896137276201632040931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52232597424850801088027287 78348896137276201632040931)
        ·
          refine ⟨117523344205914302448061397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78348896137276201632040931 117523344205914302448061397)
          ·
            refine ⟨2754453379826116463626439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 117523344205914302448061397 2754453379826116463626439)
            ·
              refine ⟨4131680069739174695439659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754453379826116463626439 4131680069739174695439659)
              ·
                refine ⟨6197520104608762043159489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4131680069739174695439659 6197520104608762043159489)
                ·
                  refine ⟨4648140078456571532369617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6197520104608762043159489 4648140078456571532369617)
                  ·
                    refine ⟨3486105058842428649277213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4648140078456571532369617 3486105058842428649277213)
                    ·
                      refine ⟨1307289397065910743478955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3486105058842428649277213 1307289397065910743478955)
                      ·
                        rfl

theorem cell23_2545937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_2545937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545937 prefixEnd_2545937 := by exact prefixLift 2545937
  have htrace : WordTrace (prefixWord ++ tailWord_2545937) baseStart_2545937 baseEnd_2545937 := by
    simpa [prefixWord, tailWord_2545937, baseEnd_2545937] using wordTrace_append hprefix tailTrace_2545937
  have hstable : (prefixWord ++ tailWord_2545937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545937).length < 2 ^ (prefixWord ++ tailWord_2545937).sum := by decide
  have hdescent : baseEnd_2545937 < baseStart_2545937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545957 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 6]
def baseStart_2545957 : Nat := 118140960795 + 2545957 * 2 ^ 59
def prefixEnd_2545957 : Nat := 4983230072969 + 3 ^ 40 * 2545957 * 2
def baseEnd_2545957 : Nat := 145255518519888962803207

theorem tailTrace_2545957 : CollatzResearch.WordTrace tailWord_2545957 prefixEnd_2545957 145255518519888962803207 := by
  unfold tailWord_2545957
  simp only [CollatzResearch.WordTrace]
  refine ⟨92858680437440078683332125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61905786958293385788888083 92858680437440078683332125)
  ·
    refine ⟨34822005164040029506249547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92858680437440078683332125 34822005164040029506249547)
    ·
      refine ⟨52233007746060044259374321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34822005164040029506249547 52233007746060044259374321)
      ·
        refine ⟨39174755809545033194530741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52233007746060044259374321 39174755809545033194530741)
        ·
          refine ⟨3672633357144846861987257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39174755809545033194530741 3672633357144846861987257)
          ·
            refine ⟨2754475017858635146490443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3672633357144846861987257 2754475017858635146490443)
            ·
              refine ⟨4131712526787952719735665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754475017858635146490443 4131712526787952719735665)
              ·
                refine ⟨3098784395090964539801749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4131712526787952719735665 3098784395090964539801749)
                ·
                  refine ⟨145255518519888962803207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3098784395090964539801749 145255518519888962803207)
                  ·
                    rfl

theorem cell23_2545957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_2545957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545957 prefixEnd_2545957 := by exact prefixLift 2545957
  have htrace : WordTrace (prefixWord ++ tailWord_2545957) baseStart_2545957 baseEnd_2545957 := by
    simpa [prefixWord, tailWord_2545957, baseEnd_2545957] using wordTrace_append hprefix tailTrace_2545957
  have hstable : (prefixWord ++ tailWord_2545957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545957).length < 2 ^ (prefixWord ++ tailWord_2545957).sum := by decide
  have hdescent : baseEnd_2545957 < baseStart_2545957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545977 : List Nat := [1, 2, 1, 6, 1, 1, 1, 2, 1, 5, 2]
def baseStart_2545977 : Nat := 118140960795 + 2545977 * 2 ^ 59
def prefixEnd_2545977 : Nat := 4983230072969 + 3 ^ 40 * 2545977 * 2
def baseEnd_2545977 : Nat := 1307309936292090586978771

theorem tailTrace_2545977 : CollatzResearch.WordTrace tailWord_2545977 prefixEnd_2545977 1307309936292090586978771 := by
  unfold tailWord_2545977
  simp only [CollatzResearch.WordTrace]
  refine ⟨92859409897367622099060185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61906273264911748066040123 92859409897367622099060185)
  ·
    refine ⟨69644557423025716574295139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92859409897367622099060185 69644557423025716574295139)
    ·
      refine ⟨104466836134538574861442709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69644557423025716574295139 104466836134538574861442709)
      ·
        refine ⟨4896882943806495696630127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 104466836134538574861442709 4896882943806495696630127)
        ·
          refine ⟨7345324415709743544945191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4896882943806495696630127 7345324415709743544945191)
          ·
            refine ⟨11017986623564615317417787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7345324415709743544945191 11017986623564615317417787)
            ·
              refine ⟨16526979935346922976126681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11017986623564615317417787 16526979935346922976126681)
              ·
                refine ⟨12395234951510192232095011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16526979935346922976126681 12395234951510192232095011)
                ·
                  refine ⟨18592852427265288348142517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12395234951510192232095011 18592852427265288348142517)
                  ·
                    refine ⟨1743079915056120782638361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18592852427265288348142517 1743079915056120782638361)
                    ·
                      refine ⟨1307309936292090586978771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1743079915056120782638361 1307309936292090586978771)
                      ·
                        rfl

theorem cell23_2545977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_2545977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545977 prefixEnd_2545977 := by exact prefixLift 2545977
  have htrace : WordTrace (prefixWord ++ tailWord_2545977) baseStart_2545977 baseEnd_2545977 := by
    simpa [prefixWord, tailWord_2545977, baseEnd_2545977] using wordTrace_append hprefix tailTrace_2545977
  have hstable : (prefixWord ++ tailWord_2545977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545977).length < 2 ^ (prefixWord ++ tailWord_2545977).sum := by decide
  have hdescent : baseEnd_2545977 < baseStart_2545977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2545993 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 5]
def baseStart_2545993 : Nat := 118140960795 + 2545993 * 2 ^ 59
def prefixEnd_2545993 : Nat := 4983230072969 + 3 ^ 40 * 2545993 * 2
def baseEnd_2545993 : Nat := 1307318151982562524378697

theorem tailTrace_2545993 : CollatzResearch.WordTrace tailWord_2545993 prefixEnd_2545993 1307318151982562524378697 := by
  unfold tailWord_2545993
  simp only [CollatzResearch.WordTrace]
  refine ⟨92859993465309656831642633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61906662310206437887761755 92859993465309656831642633)
  ·
    refine ⟨69644995098982242623731975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92859993465309656831642633 69644995098982242623731975)
    ·
      refine ⟨104467492648473363935597963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69644995098982242623731975 104467492648473363935597963)
      ·
        refine ⟨156701238972710045903396945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104467492648473363935597963 156701238972710045903396945)
        ·
          refine ⟨117525929229532534427547709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156701238972710045903396945 117525929229532534427547709)
          ·
            refine ⟨44072223461074700410330391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 117525929229532534427547709 44072223461074700410330391)
            ·
              refine ⟨66108335191612050615495587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44072223461074700410330391 66108335191612050615495587)
              ·
                refine ⟨99162502787418075923243381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66108335191612050615495587 99162502787418075923243381)
                ·
                  refine ⟨9296484636320444617804067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99162502787418075923243381 9296484636320444617804067)
                  ·
                    refine ⟨13944726954480666926706101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9296484636320444617804067 13944726954480666926706101)
                    ·
                      refine ⟨1307318151982562524378697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13944726954480666926706101 1307318151982562524378697)
                      ·
                        rfl

theorem cell23_2545993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 5, 1, 5].length) (baseStart_2545993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2545993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2545993 prefixEnd_2545993 := by exact prefixLift 2545993
  have htrace : WordTrace (prefixWord ++ tailWord_2545993) baseStart_2545993 baseEnd_2545993 := by
    simpa [prefixWord, tailWord_2545993, baseEnd_2545993] using wordTrace_append hprefix tailTrace_2545993
  have hstable : (prefixWord ++ tailWord_2545993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2545993).length < 2 ^ (prefixWord ++ tailWord_2545993).sum := by decide
  have hdescent : baseEnd_2545993 < baseStart_2545993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2545993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546000 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 4, 4]
def baseStart_2546000 : Nat := 118140960795 + 2546000 * 2 ^ 59
def prefixEnd_2546000 : Nat := 4983230072969 + 3 ^ 40 * 2546000 * 2
def baseEnd_2546000 : Nat := 435773915449047998997055

theorem tailTrace_2546000 : CollatzResearch.WordTrace tailWord_2546000 prefixEnd_2546000 435773915449047998997055 := by
  unfold tailWord_2546000
  simp only [CollatzResearch.WordTrace]
  refine ⟨46430124388142148513573727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61906832517522864684764969 46430124388142148513573727)
  ·
    refine ⟨69645186582213222770360591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46430124388142148513573727 69645186582213222770360591)
    ·
      refine ⟨104467779873319834155540887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69645186582213222770360591 104467779873319834155540887)
      ·
        refine ⟨156701669809979751233311331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104467779873319834155540887 156701669809979751233311331)
        ·
          refine ⟨235052504714969626849966997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156701669809979751233311331 235052504714969626849966997)
          ·
            refine ⟨11018086158514201258592203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 235052504714969626849966997 11018086158514201258592203)
            ·
              refine ⟨16527129237771301887888305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11018086158514201258592203 16527129237771301887888305)
              ·
                refine ⟨12395346928328476415916229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16527129237771301887888305 12395346928328476415916229)
                ·
                  refine ⟨2324127549061589327984293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12395346928328476415916229 2324127549061589327984293)
                  ·
                    refine ⟨435773915449047998997055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2324127549061589327984293 435773915449047998997055)
                    ·
                      rfl

theorem cell23_2546000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 4, 4].length) (baseStart_2546000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546000 prefixEnd_2546000 := by exact prefixLift 2546000
  have htrace : WordTrace (prefixWord ++ tailWord_2546000) baseStart_2546000 baseEnd_2546000 := by
    simpa [prefixWord, tailWord_2546000, baseEnd_2546000] using wordTrace_append hprefix tailTrace_2546000
  have hstable : (prefixWord ++ tailWord_2546000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546000).length < 2 ^ (prefixWord ++ tailWord_2546000).sum := by decide
  have hdescent : baseEnd_2546000 < baseStart_2546000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546001 : List Nat := [1, 2, 2, 1, 4, 4, 1, 3, 1, 1, 3]
def baseStart_2546001 : Nat := 118140960795 + 2546001 * 2 ^ 59
def prefixEnd_2546001 : Nat := 4983230072969 + 3 ^ 40 * 2546001 * 2
def baseEnd_2546001 : Nat := 1307322259827798493078661

theorem tailTrace_2546001 : CollatzResearch.WordTrace tailWord_2546001 prefixEnd_2546001 1307322259827798493078661 := by
  unfold tailWord_2546001
  simp only [CollatzResearch.WordTrace]
  refine ⟨92860285249280674197933857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61906856832853782798622571 92860285249280674197933857)
  ·
    refine ⟨69645213936960505648450393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92860285249280674197933857 69645213936960505648450393)
    ·
      refine ⟨52233910452720379236337795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69645213936960505648450393 52233910452720379236337795)
      ·
        refine ⟨78350865679080568854506693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52233910452720379236337795 78350865679080568854506693)
        ·
          refine ⟨14690787314827606660220005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78350865679080568854506693 14690787314827606660220005)
          ·
            refine ⟨2754522621530176248791251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14690787314827606660220005 2754522621530176248791251)
            ·
              refine ⟨4131783932295264373186877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754522621530176248791251 4131783932295264373186877)
              ·
                refine ⟨1549418974610724139945079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4131783932295264373186877 1549418974610724139945079)
                ·
                  refine ⟨2324128461916086209917619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549418974610724139945079 2324128461916086209917619)
                  ·
                    refine ⟨3486192692874129314876429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2324128461916086209917619 3486192692874129314876429)
                    ·
                      refine ⟨1307322259827798493078661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3486192692874129314876429 1307322259827798493078661)
                      ·
                        rfl

theorem cell23_2546001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 3, 1, 1, 3].length) (baseStart_2546001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546001 prefixEnd_2546001 := by exact prefixLift 2546001
  have htrace : WordTrace (prefixWord ++ tailWord_2546001) baseStart_2546001 baseEnd_2546001 := by
    simpa [prefixWord, tailWord_2546001, baseEnd_2546001] using wordTrace_append hprefix tailTrace_2546001
  have hstable : (prefixWord ++ tailWord_2546001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546001).length < 2 ^ (prefixWord ++ tailWord_2546001).sum := by decide
  have hdescent : baseEnd_2546001 < baseStart_2546001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546010 : List Nat := [3, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3]
def baseStart_2546010 : Nat := 118140960795 + 2546010 * 2 ^ 59
def prefixEnd_2546010 : Nat := 4983230072969 + 3 ^ 40 * 2546010 * 2
def baseEnd_2546010 : Nat := 1307326881153688957866119

theorem tailTrace_2546010 : CollatzResearch.WordTrace tailWord_2546010 prefixEnd_2546010 1307326881153688957866119 := by
  unfold tailWord_2546010
  simp only [CollatzResearch.WordTrace]
  refine ⟨23215153376562017183752871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61907075670832045823340989 23215153376562017183752871)
  ·
    refine ⟨34822730064843025775629307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23215153376562017183752871 34822730064843025775629307)
    ·
      refine ⟨52234095097264538663443961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34822730064843025775629307 52234095097264538663443961)
      ·
        refine ⟨39175571322948403997582971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52234095097264538663443961 39175571322948403997582971)
        ·
          refine ⟨58763356984422605996374457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39175571322948403997582971 58763356984422605996374457)
          ·
            refine ⟨44072517738316954497280843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58763356984422605996374457 44072517738316954497280843)
            ·
              refine ⟨66108776607475431745921265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44072517738316954497280843 66108776607475431745921265)
              ·
                refine ⟨49581582455606573809440949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66108776607475431745921265 49581582455606573809440949)
                ·
                  refine ⟨4648273355213116294635089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49581582455606573809440949 4648273355213116294635089)
                  ·
                    refine ⟨3486205016409837220976317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4648273355213116294635089 3486205016409837220976317)
                    ·
                      refine ⟨1307326881153688957866119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3486205016409837220976317 1307326881153688957866119)
                      ·
                        rfl

theorem cell23_2546010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_2546010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546010 prefixEnd_2546010 := by exact prefixLift 2546010
  have htrace : WordTrace (prefixWord ++ tailWord_2546010) baseStart_2546010 baseEnd_2546010 := by
    simpa [prefixWord, tailWord_2546010, baseEnd_2546010] using wordTrace_append hprefix tailTrace_2546010
  have hstable : (prefixWord ++ tailWord_2546010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546010).length < 2 ^ (prefixWord ++ tailWord_2546010).sum := by decide
  have hdescent : baseEnd_2546010 < baseStart_2546010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546018 : List Nat := [3, 3, 2, 1, 1, 3, 3, 2, 1, 1, 3]
def baseStart_2546018 : Nat := 118140960795 + 2546018 * 2 ^ 59
def prefixEnd_2546018 : Nat := 4983230072969 + 3 ^ 40 * 2546018 * 2
def baseEnd_2546018 : Nat := 1307330988998924926566083

theorem tailTrace_2546018 : CollatzResearch.WordTrace tailWord_2546018 prefixEnd_2546018 1307330988998924926566083 := by
  unfold tailWord_2546018
  simp only [CollatzResearch.WordTrace]
  refine ⟨23215226322554771525325677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61907270193479390734201805 23215226322554771525325677)
  ·
    refine ⟨8705709870958039321997129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23215226322554771525325677 8705709870958039321997129)
    ·
      refine ⟨6529282403218529491497847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8705709870958039321997129 6529282403218529491497847)
      ·
        refine ⟨9793923604827794237246771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6529282403218529491497847 9793923604827794237246771)
        ·
          refine ⟨14690885407241691355870157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9793923604827794237246771 14690885407241691355870157)
          ·
            refine ⟨5509082027715634258451309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14690885407241691355870157 5509082027715634258451309)
            ·
              refine ⟨2065905760393362846919241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5509082027715634258451309 2065905760393362846919241)
              ·
                refine ⟨1549429320295022135189431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2065905760393362846919241 1549429320295022135189431)
                ·
                  refine ⟨2324143980442533202784147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549429320295022135189431 2324143980442533202784147)
                  ·
                    refine ⟨3486215970663799804176221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2324143980442533202784147 3486215970663799804176221)
                    ·
                      refine ⟨1307330988998924926566083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3486215970663799804176221 1307330988998924926566083)
                      ·
                        rfl

theorem cell23_2546018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 3, 2, 1, 1, 3].length) (baseStart_2546018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546018 prefixEnd_2546018 := by exact prefixLift 2546018
  have htrace : WordTrace (prefixWord ++ tailWord_2546018) baseStart_2546018 baseEnd_2546018 := by
    simpa [prefixWord, tailWord_2546018, baseEnd_2546018] using wordTrace_append hprefix tailTrace_2546018
  have hstable : (prefixWord ++ tailWord_2546018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546018).length < 2 ^ (prefixWord ++ tailWord_2546018).sum := by decide
  have hdescent : baseEnd_2546018 < baseStart_2546018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546033 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_2546033 : Nat := 118140960795 + 2546033 * 2 ^ 59
def prefixEnd_2546033 : Nat := 4983230072969 + 3 ^ 40 * 2546033 * 2
def baseEnd_2546033 : Nat := 1307338691208742367878513

theorem tailTrace_2546033 : CollatzResearch.WordTrace tailWord_2546033 prefixEnd_2546033 1307338691208742367878513 := by
  unfold tailWord_2546033
  simp only [CollatzResearch.WordTrace]
  refine ⟨92861452385164743663098753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61907634923443162442065835 92861452385164743663098753)
  ·
    refine ⟨69646089288873557747324065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92861452385164743663098753 69646089288873557747324065)
    ·
      refine ⟨52234566966655168310493049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69646089288873557747324065 52234566966655168310493049)
      ·
        refine ⟨39175925224991376232869787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52234566966655168310493049 39175925224991376232869787)
        ·
          refine ⟨58763887837487064349304681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39175925224991376232869787 58763887837487064349304681)
          ·
            refine ⟨44072915878115298261978511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58763887837487064349304681 44072915878115298261978511)
            ·
              refine ⟨66109373817172947392967767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44072915878115298261978511 66109373817172947392967767)
              ·
                refine ⟨99164060725759421089451651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66109373817172947392967767 99164060725759421089451651)
                ·
                  refine ⟨148746091088639131634177477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99164060725759421089451651 148746091088639131634177477)
                  ·
                    refine ⟨27889892079119837181408277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 148746091088639131634177477 27889892079119837181408277)
                    ·
                      refine ⟨1307338691208742367878513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27889892079119837181408277 1307338691208742367878513)
                      ·
                        rfl

theorem cell23_2546033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_2546033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546033 prefixEnd_2546033 := by exact prefixLift 2546033
  have htrace : WordTrace (prefixWord ++ tailWord_2546033) baseStart_2546033 baseEnd_2546033 := by
    simpa [prefixWord, tailWord_2546033, baseEnd_2546033] using wordTrace_append hprefix tailTrace_2546033
  have hstable : (prefixWord ++ tailWord_2546033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546033).length < 2 ^ (prefixWord ++ tailWord_2546033).sum := by decide
  have hdescent : baseEnd_2546033 < baseStart_2546033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546034 : List Nat := [3, 2, 1, 2, 1, 3, 4, 1, 2, 4]
def baseStart_2546034 : Nat := 118140960795 + 2546034 * 2 ^ 59
def prefixEnd_2546034 : Nat := 4983230072969 + 3 ^ 40 * 2546034 * 2
def baseEnd_2546034 : Nat := 435779734896465621322003

theorem tailTrace_2546034 : CollatzResearch.WordTrace tailWord_2546034 prefixEnd_2546034 435779734896465621322003 := by
  unfold tailWord_2546034
  simp only [CollatzResearch.WordTrace]
  refine ⟨23215372214540280208471289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61907659238774080555923437 23215372214540280208471289)
  ·
    refine ⟨17411529160905210156353467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23215372214540280208471289 17411529160905210156353467)
    ·
      refine ⟨26117293741357815234530201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17411529160905210156353467 26117293741357815234530201)
      ·
        refine ⟨19587970306018361425897651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26117293741357815234530201 19587970306018361425897651)
        ·
          refine ⟨29381955459027542138846477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19587970306018361425897651 29381955459027542138846477)
          ·
            refine ⟨11018233297135328302067429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29381955459027542138846477 11018233297135328302067429)
            ·
              refine ⟨2065918743212874056637643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11018233297135328302067429 2065918743212874056637643)
              ·
                refine ⟨3098878114819311084956465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2065918743212874056637643 3098878114819311084956465)
                ·
                  refine ⟨2324158586114483313717349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3098878114819311084956465 2324158586114483313717349)
                  ·
                    refine ⟨435779734896465621322003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2324158586114483313717349 435779734896465621322003)
                    ·
                      rfl

theorem cell23_2546034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_2546034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546034 prefixEnd_2546034 := by exact prefixLift 2546034
  have htrace : WordTrace (prefixWord ++ tailWord_2546034) baseStart_2546034 baseEnd_2546034 := by
    simpa [prefixWord, tailWord_2546034, baseEnd_2546034] using wordTrace_append hprefix tailTrace_2546034
  have hstable : (prefixWord ++ tailWord_2546034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546034).length < 2 ^ (prefixWord ++ tailWord_2546034).sum := by decide
  have hdescent : baseEnd_2546034 < baseStart_2546034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546038 : List Nat := [5, 1, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_2546038 : Nat := 118140960795 + 2546038 * 2 ^ 59
def prefixEnd_2546038 : Nat := 4983230072969 + 3 ^ 40 * 2546038 * 2
def baseEnd_2546038 : Nat := 435780419537338282771997

theorem tailTrace_2546038 : CollatzResearch.WordTrace tailWord_2546038 prefixEnd_2546038 435780419537338282771997 := by
  unfold tailWord_2546038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5803852171884164344814423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61907756500097753011353845 5803852171884164344814423)
  ·
    refine ⟨8705778257826246517221635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5803852171884164344814423 8705778257826246517221635)
    ·
      refine ⟨13058667386739369775832453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8705778257826246517221635 13058667386739369775832453)
      ·
        refine ⟨2448500135013631832968585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13058667386739369775832453 2448500135013631832968585)
        ·
          refine ⟨1836375101260223874726439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2448500135013631832968585 1836375101260223874726439)
          ·
            refine ⟨2754562651890335812089659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836375101260223874726439 2754562651890335812089659)
            ·
              refine ⟨4131843977835503718134489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2754562651890335812089659 4131843977835503718134489)
              ·
                refine ⟨3098882983376627788600867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4131843977835503718134489 3098882983376627788600867)
                ·
                  refine ⟨4648324475064941682901301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3098882983376627788600867 4648324475064941682901301)
                  ·
                    refine ⟨435780419537338282771997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4648324475064941682901301 435780419537338282771997)
                    ·
                      rfl

theorem cell23_2546038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_2546038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546038 prefixEnd_2546038 := by exact prefixLift 2546038
  have htrace : WordTrace (prefixWord ++ tailWord_2546038) baseStart_2546038 baseEnd_2546038 := by
    simpa [prefixWord, tailWord_2546038, baseEnd_2546038] using wordTrace_append hprefix tailTrace_2546038
  have hstable : (prefixWord ++ tailWord_2546038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546038).length < 2 ^ (prefixWord ++ tailWord_2546038).sum := by decide
  have hdescent : baseEnd_2546038 < baseStart_2546038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546057 : List Nat := [1, 2, 1, 1, 6, 2, 1, 2, 1, 3, 3]
def baseStart_2546057 : Nat := 118140960795 + 2546057 * 2 ^ 59
def prefixEnd_2546057 : Nat := 4983230072969 + 3 ^ 40 * 2546057 * 2
def baseEnd_2546057 : Nat := 1307351014744450273978403

theorem tailTrace_2546057 : CollatzResearch.WordTrace tailWord_2546057 prefixEnd_2546057 1307351014744450273978403 := by
  unfold tailWord_2546057
  simp only [CollatzResearch.WordTrace]
  refine ⟨92862327737077795761972425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61908218491385197174648283 92862327737077795761972425)
  ·
    refine ⟨69646745802808346821479319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92862327737077795761972425 69646745802808346821479319)
    ·
      refine ⟨104470118704212520232218979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69646745802808346821479319 104470118704212520232218979)
      ·
        refine ⟨156705178056318780348328469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104470118704212520232218979 156705178056318780348328469)
        ·
          refine ⟨7345555221389942828827897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 156705178056318780348328469 7345555221389942828827897)
          ·
            refine ⟨5509166416042457121620923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7345555221389942828827897 5509166416042457121620923)
            ·
              refine ⟨8263749624063685682431385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5509166416042457121620923 8263749624063685682431385)
              ·
                refine ⟨6197812218047764261823539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8263749624063685682431385 6197812218047764261823539)
                ·
                  refine ⟨9296718327071646392735309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6197812218047764261823539 9296718327071646392735309)
                  ·
                    refine ⟨3486269372651867397275741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9296718327071646392735309 3486269372651867397275741)
                    ·
                      refine ⟨1307351014744450273978403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3486269372651867397275741 1307351014744450273978403)
                      ·
                        rfl

theorem cell23_2546057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 1, 2, 1, 3, 3].length) (baseStart_2546057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546057 prefixEnd_2546057 := by exact prefixLift 2546057
  have htrace : WordTrace (prefixWord ++ tailWord_2546057) baseStart_2546057 baseEnd_2546057 := by
    simpa [prefixWord, tailWord_2546057, baseEnd_2546057] using wordTrace_append hprefix tailTrace_2546057
  have hstable : (prefixWord ++ tailWord_2546057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546057).length < 2 ^ (prefixWord ++ tailWord_2546057).sum := by decide
  have hdescent : baseEnd_2546057 < baseStart_2546057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546074 : List Nat := [3, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3]
def baseStart_2546074 : Nat := 118140960795 + 2546074 * 2 ^ 59
def prefixEnd_2546074 : Nat := 4983230072969 + 3 ^ 40 * 2546074 * 2
def baseEnd_2546074 : Nat := 1307359743915576707465825

theorem tailTrace_2546074 : CollatzResearch.WordTrace tailWord_2546074 prefixEnd_2546074 1307359743915576707465825 := by
  unfold tailWord_2546074
  simp only [CollatzResearch.WordTrace]
  refine ⟨23215736944504051916335319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61908631852010805110227517 23215736944504051916335319)
  ·
    refine ⟨34823605416756077874502979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23215736944504051916335319 34823605416756077874502979)
    ·
      refine ⟨52235408125134116811754469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34823605416756077874502979 52235408125134116811754469)
      ·
        refine ⟨9794139023462646902203963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52235408125134116811754469 9794139023462646902203963)
        ·
          refine ⟨14691208535193970353305945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9794139023462646902203963 14691208535193970353305945)
          ·
            refine ⟨11018406401395477764979459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14691208535193970353305945 11018406401395477764979459)
            ·
              refine ⟨16527609602093216647469189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11018406401395477764979459 16527609602093216647469189)
              ·
                refine ⟨3098926800392478121400473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16527609602093216647469189 3098926800392478121400473)
                ·
                  refine ⟨2324195100294358591050355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3098926800392478121400473 2324195100294358591050355)
                  ·
                    refine ⟨3486292650441537886575533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2324195100294358591050355 3486292650441537886575533)
                    ·
                      refine ⟨1307359743915576707465825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3486292650441537886575533 1307359743915576707465825)
                      ·
                        rfl

theorem cell23_2546074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_2546074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546074 prefixEnd_2546074 := by exact prefixLift 2546074
  have htrace : WordTrace (prefixWord ++ tailWord_2546074) baseStart_2546074 baseEnd_2546074 := by
    simpa [prefixWord, tailWord_2546074, baseEnd_2546074] using wordTrace_append hprefix tailTrace_2546074
  have hstable : (prefixWord ++ tailWord_2546074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546074).length < 2 ^ (prefixWord ++ tailWord_2546074).sum := by decide
  have hdescent : baseEnd_2546074 < baseStart_2546074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546080 : List Nat := [2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 4]
def baseStart_2546080 : Nat := 118140960795 + 2546080 * 2 ^ 59
def prefixEnd_2546080 : Nat := 4983230072969 + 3 ^ 40 * 2546080 * 2
def baseEnd_2546080 : Nat := 1307362824799503683990797

theorem tailTrace_2546080 : CollatzResearch.WordTrace tailWord_2546080 prefixEnd_2546080 1307362824799503683990797 := by
  unfold tailWord_2546080
  simp only [CollatzResearch.WordTrace]
  refine ⟨46431583307997235345029847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61908777743996313793373129 46431583307997235345029847)
  ·
    refine ⟨69647374961995853017544771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46431583307997235345029847 69647374961995853017544771)
    ·
      refine ⟨104471062442993779526317157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69647374961995853017544771 104471062442993779526317157)
      ·
        refine ⟨19588324208061333661184467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104471062442993779526317157 19588324208061333661184467)
        ·
          refine ⟨29382486312092000491776701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19588324208061333661184467 29382486312092000491776701)
          ·
            refine ⟨11018432367034500184416263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29382486312092000491776701 11018432367034500184416263)
            ·
              refine ⟨16527648550551750276624395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11018432367034500184416263 16527648550551750276624395)
              ·
                refine ⟨24791472825827625414936593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16527648550551750276624395 24791472825827625414936593)
                ·
                  refine ⟨18593604619370719061202445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24791472825827625414936593 18593604619370719061202445)
                  ·
                    refine ⟨6972601732264019647950917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18593604619370719061202445 6972601732264019647950917)
                    ·
                      refine ⟨1307362824799503683990797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6972601732264019647950917 1307362824799503683990797)
                      ·
                        rfl

theorem cell23_2546080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_2546080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546080 prefixEnd_2546080 := by exact prefixLift 2546080
  have htrace : WordTrace (prefixWord ++ tailWord_2546080) baseStart_2546080 baseEnd_2546080 := by
    simpa [prefixWord, tailWord_2546080, baseEnd_2546080] using wordTrace_append hprefix tailTrace_2546080
  have hstable : (prefixWord ++ tailWord_2546080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546080).length < 2 ^ (prefixWord ++ tailWord_2546080).sum := by decide
  have hdescent : baseEnd_2546080 < baseStart_2546080 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546137 : List Nat := [1, 2, 1, 2, 4, 1, 1, 6, 5]
def baseStart_2546137 : Nat := 118140960795 + 2546137 * 2 ^ 59
def prefixEnd_2546137 : Nat := 4983230072969 + 3 ^ 40 * 2546137 * 2
def baseEnd_2546137 : Nat := 145265788132978884553115

theorem tailTrace_2546137 : CollatzResearch.WordTrace tailWord_2546137 prefixEnd_2546137 145265788132978884553115 := by
  unfold tailWord_2546137
  simp only [CollatzResearch.WordTrace]
  refine ⟨92865245576787969424884665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61910163717858646283256443 92865245576787969424884665)
  ·
    refine ⟨69648934182590977068663499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92865245576787969424884665 69648934182590977068663499)
    ·
      refine ⟨104473401273886465602995249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69648934182590977068663499 104473401273886465602995249)
      ·
        refine ⟨78355050955414849202246437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104473401273886465602995249 78355050955414849202246437)
        ·
          refine ⟨14691572054140284225421207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78355050955414849202246437 14691572054140284225421207)
          ·
            refine ⟨22037358081210426338131811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14691572054140284225421207 22037358081210426338131811)
            ·
              refine ⟨33056037121815639507197717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22037358081210426338131811 33056037121815639507197717)
              ·
                refine ⟨1549501740085108101899893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 33056037121815639507197717 1549501740085108101899893)
                ·
                  refine ⟨145265788132978884553115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1549501740085108101899893 145265788132978884553115)
                  ·
                    rfl

theorem cell23_2546137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 5].length) (baseStart_2546137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546137 prefixEnd_2546137 := by exact prefixLift 2546137
  have htrace : WordTrace (prefixWord ++ tailWord_2546137) baseStart_2546137 baseEnd_2546137 := by
    simpa [prefixWord, tailWord_2546137, baseEnd_2546137] using wordTrace_append hprefix tailTrace_2546137
  have hstable : (prefixWord ++ tailWord_2546137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546137).length < 2 ^ (prefixWord ++ tailWord_2546137).sum := by decide
  have hdescent : baseEnd_2546137 < baseStart_2546137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546187 : List Nat := [1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 4]
def baseStart_2546187 : Nat := 118140960795 + 2546187 * 2 ^ 59
def prefixEnd_2546187 : Nat := 4983230072969 + 3 ^ 40 * 2546187 * 2
def baseEnd_2546187 : Nat := 1307417767229534765352805

theorem tailTrace_2546187 : CollatzResearch.WordTrace tailWord_2546187 prefixEnd_2546187 1307417767229534765352805 := by
  unfold tailWord_2546187
  simp only [CollatzResearch.WordTrace]
  refine ⟨92867069226606827964204815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61911379484404551976136543 92867069226606827964204815)
  ·
    refine ⟨139300603839910241946307223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92867069226606827964204815 139300603839910241946307223)
    ·
      refine ⟨208950905759865362919460835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139300603839910241946307223 208950905759865362919460835)
      ·
        refine ⟨313426358639798044379191253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208950905759865362919460835 313426358639798044379191253)
        ·
          refine ⟨7345930280620266665137295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 313426358639798044379191253 7345930280620266665137295)
          ·
            refine ⟨11018895420930399997705943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7345930280620266665137295 11018895420930399997705943)
            ·
              refine ⟨16528343131395599996558915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11018895420930399997705943 16528343131395599996558915)
              ·
                refine ⟨24792514697093399994838373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16528343131395599996558915 24792514697093399994838373)
                ·
                  refine ⟨4648596505705012499032195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24792514697093399994838373 4648596505705012499032195)
                  ·
                    refine ⟨6972894758557518748548293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4648596505705012499032195 6972894758557518748548293)
                    ·
                      refine ⟨1307417767229534765352805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6972894758557518748548293 1307417767229534765352805)
                      ·
                        rfl

theorem cell23_2546187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 4].length) (baseStart_2546187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546187 prefixEnd_2546187 := by exact prefixLift 2546187
  have htrace : WordTrace (prefixWord ++ tailWord_2546187) baseStart_2546187 baseEnd_2546187 := by
    simpa [prefixWord, tailWord_2546187, baseEnd_2546187] using wordTrace_append hprefix tailTrace_2546187
  have hstable : (prefixWord ++ tailWord_2546187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546187).length < 2 ^ (prefixWord ++ tailWord_2546187).sum := by decide
  have hdescent : baseEnd_2546187 < baseStart_2546187 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546207 : List Nat := [1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 3]
def baseStart_2546207 : Nat := 118140960795 + 2546207 * 2 ^ 59
def prefixEnd_2546207 : Nat := 4983230072969 + 3 ^ 40 * 2546207 * 2
def baseEnd_2546207 : Nat := 1307428036842624687102713

theorem tailTrace_2546207 : CollatzResearch.WordTrace tailWord_2546207 prefixEnd_2546207 1307428036842624687102713 := by
  unfold tailWord_2546207
  simp only [CollatzResearch.WordTrace]
  refine ⟨92867798686534371379932875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61911865791022914253288583 92867798686534371379932875)
  ·
    refine ⟨139301698029801557069899313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92867798686534371379932875 139301698029801557069899313)
    ·
      refine ⟨104476273522351167802424485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139301698029801557069899313 104476273522351167802424485)
      ·
        refine ⟨19589301285440843962954591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104476273522351167802424485 19589301285440843962954591)
        ·
          refine ⟨29383951928161265944431887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19589301285440843962954591 29383951928161265944431887)
          ·
            refine ⟨44075927892241898916647831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29383951928161265944431887 44075927892241898916647831)
            ·
              refine ⟨66113891838362848374971747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44075927892241898916647831 66113891838362848374971747)
              ·
                refine ⟨99170837757544272562457621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66113891838362848374971747 99170837757544272562457621)
                ·
                  refine ⟨4648633019884887776365201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 99170837757544272562457621 4648633019884887776365201)
                  ·
                    refine ⟨3486474764913665832273901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4648633019884887776365201 3486474764913665832273901)
                    ·
                      refine ⟨1307428036842624687102713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3486474764913665832273901 1307428036842624687102713)
                      ·
                        rfl

theorem cell23_2546207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_2546207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546207 prefixEnd_2546207 := by exact prefixLift 2546207
  have htrace : WordTrace (prefixWord ++ tailWord_2546207) baseStart_2546207 baseEnd_2546207 := by
    simpa [prefixWord, tailWord_2546207, baseEnd_2546207] using wordTrace_append hprefix tailTrace_2546207
  have hstable : (prefixWord ++ tailWord_2546207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546207).length < 2 ^ (prefixWord ++ tailWord_2546207).sum := by decide
  have hdescent : baseEnd_2546207 < baseStart_2546207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546257 : List Nat := [1, 2, 2, 1, 3, 3, 1, 2, 3, 5]
def baseStart_2546257 : Nat := 118140960795 + 2546257 * 2 ^ 59
def prefixEnd_2546257 : Nat := 4983230072969 + 3 ^ 40 * 2546257 * 2
def baseEnd_2546257 : Nat := 435817903625116497159161

theorem tailTrace_2546257 : CollatzResearch.WordTrace tailWord_2546257 prefixEnd_2546257 435817903625116497159161 := by
  unfold tailWord_2546257
  simp only [CollatzResearch.WordTrace]
  refine ⟨92869622336353229919253025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61913081557568819946168683 92869622336353229919253025)
  ·
    refine ⟨69652216752264922439439769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92869622336353229919253025 69652216752264922439439769)
    ·
      refine ⟨52239162564198691829579827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69652216752264922439439769 52239162564198691829579827)
      ·
        refine ⟨78358743846298037744369741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52239162564198691829579827 78358743846298037744369741)
        ·
          refine ⟨29384528942361764154138653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78358743846298037744369741 29384528942361764154138653)
          ·
            refine ⟨11019198353385661557801995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29384528942361764154138653 11019198353385661557801995)
            ·
              refine ⟨16528797530078492336702993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11019198353385661557801995 16528797530078492336702993)
              ·
                refine ⟨12396598147558869252527245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16528797530078492336702993 12396598147558869252527245)
                ·
                  refine ⟨4648724305334575969697717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12396598147558869252527245 4648724305334575969697717)
                  ·
                    refine ⟨435817903625116497159161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4648724305334575969697717 435817903625116497159161)
                    ·
                      rfl

theorem cell23_2546257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_2546257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546257 prefixEnd_2546257 := by exact prefixLift 2546257
  have htrace : WordTrace (prefixWord ++ tailWord_2546257) baseStart_2546257 baseEnd_2546257 := by
    simpa [prefixWord, tailWord_2546257, baseEnd_2546257] using wordTrace_append hprefix tailTrace_2546257
  have hstable : (prefixWord ++ tailWord_2546257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546257).length < 2 ^ (prefixWord ++ tailWord_2546257).sum := by decide
  have hdescent : baseEnd_2546257 < baseStart_2546257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546264 : List Nat := [2, 1, 2, 2, 1, 2, 2, 2, 4, 3, 2]
def baseStart_2546264 : Nat := 118140960795 + 2546264 * 2 ^ 59
def prefixEnd_2546264 : Nat := 4983230072969 + 3 ^ 40 * 2546264 * 2
def baseEnd_2546264 : Nat := 1307457305239930964089951

theorem tailTrace_2546264 : CollatzResearch.WordTrace tailWord_2546264 prefixEnd_2546264 1307457305239930964089951 := by
  unfold tailWord_2546264
  simp only [CollatzResearch.WordTrace]
  refine ⟨46434938823663935057378923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61913251764885246743171897 46434938823663935057378923)
  ·
    refine ⟨69652408235495902586068385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46434938823663935057378923 69652408235495902586068385)
    ·
      refine ⟨52239306176621926939551289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69652408235495902586068385 52239306176621926939551289)
      ·
        refine ⟨39179479632466445204663467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52239306176621926939551289 39179479632466445204663467)
        ·
          refine ⟨58769219448699667806995201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39179479632466445204663467 58769219448699667806995201)
          ·
            refine ⟨44076914586524750855246401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58769219448699667806995201 44076914586524750855246401)
            ·
              refine ⟨33057685939893563141434801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44076914586524750855246401 33057685939893563141434801)
              ·
                refine ⟨24793264454920172356076101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33057685939893563141434801 24793264454920172356076101)
                ·
                  refine ⟨4648737085297532316764269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24793264454920172356076101 4648737085297532316764269)
                  ·
                    refine ⟨1743276406986574618786601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4648737085297532316764269 1743276406986574618786601)
                    ·
                      refine ⟨1307457305239930964089951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1743276406986574618786601 1307457305239930964089951)
                      ·
                        rfl

theorem cell23_2546264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 2, 4, 3, 2].length) (baseStart_2546264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546264 prefixEnd_2546264 := by exact prefixLift 2546264
  have htrace : WordTrace (prefixWord ++ tailWord_2546264) baseStart_2546264 baseEnd_2546264 := by
    simpa [prefixWord, tailWord_2546264, baseEnd_2546264] using wordTrace_append hprefix tailTrace_2546264
  have hstable : (prefixWord ++ tailWord_2546264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546264).length < 2 ^ (prefixWord ++ tailWord_2546264).sum := by decide
  have hdescent : baseEnd_2546264 < baseStart_2546264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546287 : List Nat := [1, 1, 2, 1, 3, 2, 4, 2, 1, 6]
def baseStart_2546287 : Nat := 118140960795 + 2546287 * 2 ^ 59
def prefixEnd_2546287 : Nat := 4983230072969 + 3 ^ 40 * 2546287 * 2
def baseEnd_2546287 : Nat := 435823038431661458034115

theorem tailTrace_2546287 : CollatzResearch.WordTrace tailWord_2546287 prefixEnd_2546287 435823038431661458034115 := by
  unfold tailWord_2546287
  simp only [CollatzResearch.WordTrace]
  refine ⟨92870716526244545042845115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61913811017496363361896743 92870716526244545042845115)
  ·
    refine ⟨139306074789366817564267673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92870716526244545042845115 139306074789366817564267673)
    ·
      refine ⟨104479556092025113173200755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139306074789366817564267673 104479556092025113173200755)
      ·
        refine ⟨156719334138037669759801133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104479556092025113173200755 156719334138037669759801133)
        ·
          refine ⟨58769750301764126159925425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156719334138037669759801133 58769750301764126159925425)
          ·
            refine ⟨44077312726323094619944069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58769750301764126159925425 44077312726323094619944069)
            ·
              refine ⟨8264496136185580241239513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 44077312726323094619944069 8264496136185580241239513)
              ·
                refine ⟨6198372102139185180929635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8264496136185580241239513 6198372102139185180929635)
                ·
                  refine ⟨9297558153208777771394453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6198372102139185180929635 9297558153208777771394453)
                  ·
                    refine ⟨435823038431661458034115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 9297558153208777771394453 435823038431661458034115)
                    ·
                      rfl

theorem cell23_2546287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 2, 1, 6].length) (baseStart_2546287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546287 prefixEnd_2546287 := by exact prefixLift 2546287
  have htrace : WordTrace (prefixWord ++ tailWord_2546287) baseStart_2546287 baseEnd_2546287 := by
    simpa [prefixWord, tailWord_2546287, baseEnd_2546287] using wordTrace_append hprefix tailTrace_2546287
  have hstable : (prefixWord ++ tailWord_2546287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546287).length < 2 ^ (prefixWord ++ tailWord_2546287).sum := by decide
  have hdescent : baseEnd_2546287 < baseStart_2546287 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546304 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 4, 4]
def baseStart_2546304 : Nat := 118140960795 + 2546304 * 2 ^ 59
def prefixEnd_2546304 : Nat := 4983230072969 + 3 ^ 40 * 2546304 * 2
def baseEnd_2546304 : Nat := 435825948155370269196589

theorem tailTrace_2546304 : CollatzResearch.WordTrace tailWord_2546304 prefixEnd_2546304 435825948155370269196589 := by
  unfold tailWord_2546304
  simp only [CollatzResearch.WordTrace]
  refine ⟨46435668283591478473106983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61914224378121971297475977 46435668283591478473106983)
  ·
    refine ⟨69653502425387217709660475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46435668283591478473106983 69653502425387217709660475)
    ·
      refine ⟨104480253638080826564490713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69653502425387217709660475 104480253638080826564490713)
      ·
        refine ⟨78360190228560619923368035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104480253638080826564490713 78360190228560619923368035)
        ·
          refine ⟨117540285342840929885052053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78360190228560619923368035 117540285342840929885052053)
          ·
            refine ⟨5509700875445668588361815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117540285342840929885052053 5509700875445668588361815)
            ·
              refine ⟨8264551313168502882542723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5509700875445668588361815 8264551313168502882542723)
              ·
                refine ⟨12396826969752754323814085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8264551313168502882542723 12396826969752754323814085)
                ·
                  refine ⟨2324405056828641435715141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12396826969752754323814085 2324405056828641435715141)
                  ·
                    refine ⟨435825948155370269196589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2324405056828641435715141 435825948155370269196589)
                    ·
                      rfl

theorem cell23_2546304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4, 4].length) (baseStart_2546304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546304 prefixEnd_2546304 := by exact prefixLift 2546304
  have htrace : WordTrace (prefixWord ++ tailWord_2546304) baseStart_2546304 baseEnd_2546304 := by
    simpa [prefixWord, tailWord_2546304, baseEnd_2546304] using wordTrace_append hprefix tailTrace_2546304
  have hstable : (prefixWord ++ tailWord_2546304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546304).length < 2 ^ (prefixWord ++ tailWord_2546304).sum := by decide
  have hdescent : baseEnd_2546304 < baseStart_2546304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546307 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 4]
def baseStart_2546307 : Nat := 118140960795 + 2546307 * 2 ^ 59
def prefixEnd_2546307 : Nat := 4983230072969 + 3 ^ 40 * 2546307 * 2
def baseEnd_2546307 : Nat := 1307479384908074295852253

theorem tailTrace_2546307 : CollatzResearch.WordTrace tailWord_2546307 prefixEnd_2546307 1307479384908074295852253 := by
  unfold tailWord_2546307
  simp only [CollatzResearch.WordTrace]
  refine ⟨92871445986172088458573175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61914297324114725639048783 92871445986172088458573175)
  ·
    refine ⟨139307168979258132687859763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92871445986172088458573175 139307168979258132687859763)
    ·
      refine ⟨208960753468887199031789645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139307168979258132687859763 208960753468887199031789645)
      ·
        refine ⟨78360282550832699636921117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208960753468887199031789645 78360282550832699636921117)
        ·
          refine ⟨29385105956562262363845419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78360282550832699636921117 29385105956562262363845419)
          ·
            refine ⟨44077658934843393545768129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29385105956562262363845419 44077658934843393545768129)
            ·
              refine ⟨33058244201132545159326097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44077658934843393545768129 33058244201132545159326097)
              ·
                refine ⟨24793683150849408869494573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33058244201132545159326097 24793683150849408869494573)
                ·
                  refine ⟨9297631181568528326060465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24793683150849408869494573 9297631181568528326060465)
                  ·
                    refine ⟨6973223386176396244545349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9297631181568528326060465 6973223386176396244545349)
                    ·
                      refine ⟨1307479384908074295852253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6973223386176396244545349 1307479384908074295852253)
                      ·
                        rfl

theorem cell23_2546307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 4].length) (baseStart_2546307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546307 prefixEnd_2546307 := by exact prefixLift 2546307
  have htrace : WordTrace (prefixWord ++ tailWord_2546307) baseStart_2546307 baseEnd_2546307 := by
    simpa [prefixWord, tailWord_2546307, baseEnd_2546307] using wordTrace_append hprefix tailTrace_2546307
  have hstable : (prefixWord ++ tailWord_2546307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546307).length < 2 ^ (prefixWord ++ tailWord_2546307).sum := by decide
  have hdescent : baseEnd_2546307 < baseStart_2546307 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546334 : List Nat := [4, 3, 1, 1, 1, 1, 3, 9]
def baseStart_2546334 : Nat := 118140960795 + 2546334 * 2 ^ 59
def prefixEnd_2546334 : Nat := 4983230072969 + 3 ^ 40 * 2546334 * 2
def baseEnd_2546334 : Nat := 48425675884657247785727

theorem tailTrace_2546334 : CollatzResearch.WordTrace tailWord_2546334 prefixEnd_2546334 48425675884657247785727 := by
  unfold tailWord_2546334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11609053844634284008725757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61914953838049514713204037 11609053844634284008725757)
  ·
    refine ⟨4353395191737856503272159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11609053844634284008725757 4353395191737856503272159)
    ·
      refine ⟨6530092787606784754908239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4353395191737856503272159 6530092787606784754908239)
      ·
        refine ⟨9795139181410177132362359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6530092787606784754908239 9795139181410177132362359)
        ·
          refine ⟨14692708772115265698543539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9795139181410177132362359 14692708772115265698543539)
          ·
            refine ⟨22039063158172898547815309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14692708772115265698543539 22039063158172898547815309)
            ·
              refine ⟨8264648684314836955430741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22039063158172898547815309 8264648684314836955430741)
              ·
                refine ⟨48425675884657247785727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8264648684314836955430741 48425675884657247785727)
                ·
                  rfl

theorem cell23_2546334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 3, 9].length) (baseStart_2546334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546334 prefixEnd_2546334 := by exact prefixLift 2546334
  have htrace : WordTrace (prefixWord ++ tailWord_2546334) baseStart_2546334 baseEnd_2546334 := by
    simpa [prefixWord, tailWord_2546334, baseEnd_2546334] using wordTrace_append hprefix tailTrace_2546334
  have hstable : (prefixWord ++ tailWord_2546334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546334).length < 2 ^ (prefixWord ++ tailWord_2546334).sum := by decide
  have hdescent : baseEnd_2546334 < baseStart_2546334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546361 : List Nat := [1, 2, 1, 4, 1, 1, 1, 6, 2, 1, 3]
def baseStart_2546361 : Nat := 118140960795 + 2546361 * 2 ^ 59
def prefixEnd_2546361 : Nat := 4983230072969 + 3 ^ 40 * 2546361 * 2
def baseEnd_2546361 : Nat := 1307507112863417084577005

theorem tailTrace_2546361 : CollatzResearch.WordTrace tailWord_2546361 prefixEnd_2546361 1307507112863417084577005 := by
  unfold tailWord_2546361
  simp only [CollatzResearch.WordTrace]
  refine ⟨92873415527976455681038937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61915610351984303787359291 92873415527976455681038937)
  ·
    refine ⟨69655061645982341760779203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92873415527976455681038937 69655061645982341760779203)
    ·
      refine ⟨104482592468973512641168805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69655061645982341760779203 104482592468973512641168805)
      ·
        refine ⟨19590486087932533620219151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104482592468973512641168805 19590486087932533620219151)
        ·
          refine ⟨29385729131898800430328727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19590486087932533620219151 29385729131898800430328727)
          ·
            refine ⟨44078593697848200645493091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29385729131898800430328727 44078593697848200645493091)
            ·
              refine ⟨66117890546772300968239637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44078593697848200645493091 66117890546772300968239637)
              ·
                refine ⟨3099276119379951607886233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 66117890546772300968239637 3099276119379951607886233)
                ·
                  refine ⟨2324457089534963705914675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3099276119379951607886233 2324457089534963705914675)
                  ·
                    refine ⟨3486685634302445558872013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2324457089534963705914675 3486685634302445558872013)
                    ·
                      refine ⟨1307507112863417084577005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3486685634302445558872013 1307507112863417084577005)
                      ·
                        rfl

theorem cell23_2546361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 6, 2, 1, 3].length) (baseStart_2546361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546361 prefixEnd_2546361 := by exact prefixLift 2546361
  have htrace : WordTrace (prefixWord ++ tailWord_2546361) baseStart_2546361 baseEnd_2546361 := by
    simpa [prefixWord, tailWord_2546361, baseEnd_2546361] using wordTrace_append hprefix tailTrace_2546361
  have hstable : (prefixWord ++ tailWord_2546361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546361).length < 2 ^ (prefixWord ++ tailWord_2546361).sum := by decide
  have hdescent : baseEnd_2546361 < baseStart_2546361 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546378 : List Nat := [3, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3]
def baseStart_2546378 : Nat := 118140960795 + 2546378 * 2 ^ 59
def prefixEnd_2546378 : Nat := 4983230072969 + 3 ^ 40 * 2546378 * 2
def baseEnd_2546378 : Nat := 1307515842034543518064427

theorem tailTrace_2546378 : CollatzResearch.WordTrace tailWord_2546378 prefixEnd_2546378 1307515842034543518064427 := by
  unfold tailWord_2546378
  simp only [CollatzResearch.WordTrace]
  refine ⟨23218508892228716896101947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61916023712609911722938525 23218508892228716896101947)
  ·
    refine ⟨34827763338343075344152921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23218508892228716896101947 34827763338343075344152921)
    ·
      refine ⟨26120822503757306508114691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34827763338343075344152921 26120822503757306508114691)
      ·
        refine ⟨39181233755635959762172037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26120822503757306508114691 39181233755635959762172037)
        ·
          refine ⟨7346481329181742455407257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39181233755635959762172037 7346481329181742455407257)
          ·
            refine ⟨5509860996886306841555443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7346481329181742455407257 5509860996886306841555443)
            ·
              refine ⟨8264791495329460262333165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5509860996886306841555443 8264791495329460262333165)
              ·
                refine ⟨3099296810748547598374937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8264791495329460262333165 3099296810748547598374937)
                ·
                  refine ⟨2324472608061410698781203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3099296810748547598374937 2324472608061410698781203)
                  ·
                    refine ⟨3486708912092116048171805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2324472608061410698781203 3486708912092116048171805)
                    ·
                      refine ⟨1307515842034543518064427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3486708912092116048171805 1307515842034543518064427)
                      ·
                        rfl

theorem cell23_2546378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 3, 2, 1, 3].length) (baseStart_2546378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546378 prefixEnd_2546378 := by exact prefixLift 2546378
  have htrace : WordTrace (prefixWord ++ tailWord_2546378) baseStart_2546378 baseEnd_2546378 := by
    simpa [prefixWord, tailWord_2546378, baseEnd_2546378] using wordTrace_append hprefix tailTrace_2546378
  have hstable : (prefixWord ++ tailWord_2546378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546378).length < 2 ^ (prefixWord ++ tailWord_2546378).sum := by decide
  have hdescent : baseEnd_2546378 < baseStart_2546378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546401 : List Nat := [1, 2, 3, 1, 4, 1, 1, 1, 3, 4, 2]
def baseStart_2546401 : Nat := 118140960795 + 2546401 * 2 ^ 59
def prefixEnd_2546401 : Nat := 4983230072969 + 3 ^ 40 * 2546401 * 2
def baseEnd_2546401 : Nat := 1307527652089596928076821

theorem tailTrace_2546401 : CollatzResearch.WordTrace tailWord_2546401 prefixEnd_2546401 1307527652089596928076821 := by
  unfold tailWord_2546401
  simp only [CollatzResearch.WordTrace]
  refine ⟨92874874447831542512495057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61916582965221028341663371 92874874447831542512495057)
  ·
    refine ⟨69656155835873656884371293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92874874447831542512495057 69656155835873656884371293)
    ·
      refine ⟨26121058438452621331639235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69656155835873656884371293 26121058438452621331639235)
      ·
        refine ⟨39181587657678931997458853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26121058438452621331639235 39181587657678931997458853)
        ·
          refine ⟨7346547685814799749523535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 39181587657678931997458853 7346547685814799749523535)
          ·
            refine ⟨11019821528722199624285303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7346547685814799749523535 11019821528722199624285303)
            ·
              refine ⟨16529732293083299436427955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11019821528722199624285303 16529732293083299436427955)
              ·
                refine ⟨24794598439624949154641933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16529732293083299436427955 24794598439624949154641933)
                ·
                  refine ⟨9297974414859355932990725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24794598439624949154641933 9297974414859355932990725)
                  ·
                    refine ⟨1743370202786129237435761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9297974414859355932990725 1743370202786129237435761)
                    ·
                      refine ⟨1307527652089596928076821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1743370202786129237435761 1307527652089596928076821)
                      ·
                        rfl

theorem cell23_2546401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_2546401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546401 prefixEnd_2546401 := by exact prefixLift 2546401
  have htrace : WordTrace (prefixWord ++ tailWord_2546401) baseStart_2546401 baseEnd_2546401 := by
    simpa [prefixWord, tailWord_2546401, baseEnd_2546401] using wordTrace_append hprefix tailTrace_2546401
  have hstable : (prefixWord ++ tailWord_2546401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546401).length < 2 ^ (prefixWord ++ tailWord_2546401).sum := by decide
  have hdescent : baseEnd_2546401 < baseStart_2546401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546404 : List Nat := [2, 3, 1, 1, 1, 4, 2, 1, 2, 1, 5]
def baseStart_2546404 : Nat := 118140960795 + 2546404 * 2 ^ 59
def prefixEnd_2546404 : Nat := 4983230072969 + 3 ^ 40 * 2546404 * 2
def baseEnd_2546404 : Nat := 1307529192531560416339307

theorem tailTrace_2546404 : CollatzResearch.WordTrace tailWord_2546404 prefixEnd_2546404 1307529192531560416339307 := by
  unfold tailWord_2546404
  simp only [CollatzResearch.WordTrace]
  refine ⟨46437491933410337012427133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61916655911213782683236177 46437491933410337012427133)
  ·
    refine ⟨17414059475028876379660175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46437491933410337012427133 17414059475028876379660175)
    ·
      refine ⟨26121089212543314569490263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17414059475028876379660175 26121089212543314569490263)
      ·
        refine ⟨39181633818814971854235395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26121089212543314569490263 39181633818814971854235395)
        ·
          refine ⟨58772450728222457781353093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39181633818814971854235395 58772450728222457781353093)
          ·
            refine ⟨11019834511541710834003705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58772450728222457781353093 11019834511541710834003705)
            ·
              refine ⟨8264875883656283125502779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11019834511541710834003705 8264875883656283125502779)
              ·
                refine ⟨12397313825484424688254169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8264875883656283125502779 12397313825484424688254169)
                ·
                  refine ⟨9297985369113318516190627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12397313825484424688254169 9297985369113318516190627)
                  ·
                    refine ⟨13946978053669977774285941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9297985369113318516190627 13946978053669977774285941)
                    ·
                      refine ⟨1307529192531560416339307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13946978053669977774285941 1307529192531560416339307)
                      ·
                        rfl

theorem cell23_2546404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_2546404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546404 prefixEnd_2546404 := by exact prefixLift 2546404
  have htrace : WordTrace (prefixWord ++ tailWord_2546404) baseStart_2546404 baseEnd_2546404 := by
    simpa [prefixWord, tailWord_2546404, baseEnd_2546404] using wordTrace_append hprefix tailTrace_2546404
  have hstable : (prefixWord ++ tailWord_2546404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546404).length < 2 ^ (prefixWord ++ tailWord_2546404).sum := by decide
  have hdescent : baseEnd_2546404 < baseStart_2546404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546405 : List Nat := [1, 3, 1, 4, 1, 3, 3, 1, 1, 3, 2]
def baseStart_2546405 : Nat := 118140960795 + 2546405 * 2 ^ 59
def prefixEnd_2546405 : Nat := 4983230072969 + 3 ^ 40 * 2546405 * 2
def baseEnd_2546405 : Nat := 1307529706012214912426803

theorem tailTrace_2546405 : CollatzResearch.WordTrace tailWord_2546405 prefixEnd_2546405 1307529706012214912426803 := by
  unfold tailWord_2546405
  simp only [CollatzResearch.WordTrace]
  refine ⟨92875020339817051195640669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61916680226544700797093779 92875020339817051195640669)
  ·
    refine ⟨34828132627431394198365251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92875020339817051195640669 34828132627431394198365251)
    ·
      refine ⟨52242198941147091297547877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34828132627431394198365251 52242198941147091297547877)
      ·
        refine ⟨9795412301465079618290227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52242198941147091297547877 9795412301465079618290227)
        ·
          refine ⟨14693118452197619427435341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9795412301465079618290227 14693118452197619427435341)
          ·
            refine ⟨5509919419574107285288253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14693118452197619427435341 5509919419574107285288253)
            ·
              refine ⟨2066219782340290231983095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5509919419574107285288253 2066219782340290231983095)
              ·
                refine ⟨3099329673510435347974643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066219782340290231983095 3099329673510435347974643)
                ·
                  refine ⟨4648994510265653021961965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099329673510435347974643 4648994510265653021961965)
                  ·
                    refine ⟨1743372941349619883235737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4648994510265653021961965 1743372941349619883235737)
                    ·
                      refine ⟨1307529706012214912426803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1743372941349619883235737 1307529706012214912426803)
                      ·
                        rfl

theorem cell23_2546405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_2546405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546405 prefixEnd_2546405 := by exact prefixLift 2546405
  have htrace : WordTrace (prefixWord ++ tailWord_2546405) baseStart_2546405 baseEnd_2546405 := by
    simpa [prefixWord, tailWord_2546405, baseEnd_2546405] using wordTrace_append hprefix tailTrace_2546405
  have hstable : (prefixWord ++ tailWord_2546405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546405).length < 2 ^ (prefixWord ++ tailWord_2546405).sum := by decide
  have hdescent : baseEnd_2546405 < baseStart_2546405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546504 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 2, 4, 4]
def baseStart_2546504 : Nat := 118140960795 + 2546504 * 2 ^ 59
def prefixEnd_2546504 : Nat := 4983230072969 + 3 ^ 40 * 2546504 * 2
def baseEnd_2546504 : Nat := 1307580540597010025088847

theorem tailTrace_2546504 : CollatzResearch.WordTrace tailWord_2546504 prefixEnd_2546504 1307580540597010025088847 := by
  unfold tailWord_2546504
  simp only [CollatzResearch.WordTrace]
  refine ⟨46439315583229195551747283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61919087444305594068996377 46439315583229195551747283)
  ·
    refine ⟨69658973374843793327620925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46439315583229195551747283 69658973374843793327620925)
    ·
      refine ⟨26122115015566422497857847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69658973374843793327620925 26122115015566422497857847)
      ·
        refine ⟨39183172523349633746786771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26122115015566422497857847 39183172523349633746786771)
        ·
          refine ⟨58774758785024450620180157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39183172523349633746786771 58774758785024450620180157)
          ·
            refine ⟨22040534544384168982567559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58774758785024450620180157 22040534544384168982567559)
            ·
              refine ⟨33060801816576253473851339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22040534544384168982567559 33060801816576253473851339)
              ·
                refine ⟨49591202724864380210777009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33060801816576253473851339 49591202724864380210777009)
                ·
                  refine ⟨37193402043648285158082757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49591202724864380210777009 37193402043648285158082757)
                  ·
                    refine ⟨6973762883184053467140517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 37193402043648285158082757 6973762883184053467140517)
                    ·
                      refine ⟨1307580540597010025088847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6973762883184053467140517 1307580540597010025088847)
                      ·
                        rfl

theorem cell23_2546504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_2546504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546504 prefixEnd_2546504 := by exact prefixLift 2546504
  have htrace : WordTrace (prefixWord ++ tailWord_2546504) baseStart_2546504 baseEnd_2546504 := by
    simpa [prefixWord, tailWord_2546504, baseEnd_2546504] using wordTrace_append hprefix tailTrace_2546504
  have hstable : (prefixWord ++ tailWord_2546504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546504).length < 2 ^ (prefixWord ++ tailWord_2546504).sum := by decide
  have hdescent : baseEnd_2546504 < baseStart_2546504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546514 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 10]
def baseStart_2546514 : Nat := 118140960795 + 2546514 * 2 ^ 59
def prefixEnd_2546514 : Nat := 4983230072969 + 3 ^ 40 * 2546514 * 2
def baseEnd_2546514 : Nat := 145287297267061665107089

theorem tailTrace_2546514 : CollatzResearch.WordTrace tailWord_2546514 prefixEnd_2546514 145287297267061665107089 := by
  unfold tailWord_2546514
  simp only [CollatzResearch.WordTrace]
  refine ⟨23219748974105540702839649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61919330597614775207572397 23219748974105540702839649)
  ·
    refine ⟨17414811730579155527129737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23219748974105540702839649 17414811730579155527129737)
    ·
      refine ⟨13061108797934366645347303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17414811730579155527129737 13061108797934366645347303)
      ·
        refine ⟨19591663196901549968020955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13061108797934366645347303 19591663196901549968020955)
        ·
          refine ⟨29387494795352324952031433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19591663196901549968020955 29387494795352324952031433)
          ·
            refine ⟨22040621096514243714023575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29387494795352324952031433 22040621096514243714023575)
            ·
              refine ⟨33060931644771365571035363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22040621096514243714023575 33060931644771365571035363)
              ·
                refine ⟨49591397467157048356553045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33060931644771365571035363 49591397467157048356553045)
                ·
                  refine ⟨145287297267061665107089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 49591397467157048356553045 145287297267061665107089)
                  ·
                    rfl

theorem cell23_2546514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 10].length) (baseStart_2546514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546514 prefixEnd_2546514 := by exact prefixLift 2546514
  have htrace : WordTrace (prefixWord ++ tailWord_2546514) baseStart_2546514 baseEnd_2546514 := by
    simpa [prefixWord, tailWord_2546514, baseEnd_2546514] using wordTrace_append hprefix tailTrace_2546514
  have hstable : (prefixWord ++ tailWord_2546514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546514).length < 2 ^ (prefixWord ++ tailWord_2546514).sum := by decide
  have hdescent : baseEnd_2546514 < baseStart_2546514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546551 : List Nat := [1, 1, 3, 1, 1, 2, 1, 3, 3, 5, 2]
def baseStart_2546551 : Nat := 118140960795 + 2546551 * 2 ^ 59
def prefixEnd_2546551 : Nat := 4983230072969 + 3 ^ 40 * 2546551 * 2
def baseEnd_2546551 : Nat := 1307604674187771341201131

theorem tailTrace_2546551 : CollatzResearch.WordTrace tailWord_2546551 prefixEnd_2546551 1307604674187771341201131 := by
  unfold tailWord_2546551
  simp only [CollatzResearch.WordTrace]
  refine ⟨92880345397288118130455507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61920230264858745420303671 92880345397288118130455507)
  ·
    refine ⟨139320518095932177195683261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92880345397288118130455507 139320518095932177195683261)
    ·
      refine ⟨52245194285974566448381223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139320518095932177195683261 52245194285974566448381223)
      ·
        refine ⟨78367791428961849672571835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52245194285974566448381223 78367791428961849672571835)
        ·
          refine ⟨117551687143442774508857753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78367791428961849672571835 117551687143442774508857753)
          ·
            refine ⟨88163765357582080881643315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117551687143442774508857753 88163765357582080881643315)
            ·
              refine ⟨132245648036373121322464973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88163765357582080881643315 132245648036373121322464973)
              ·
                refine ⟨49592118013639920495924365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132245648036373121322464973 49592118013639920495924365)
                ·
                  refine ⟨18597044255114970185971637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49592118013639920495924365 18597044255114970185971637)
                  ·
                    refine ⟨1743472898917028454934841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18597044255114970185971637 1743472898917028454934841)
                    ·
                      refine ⟨1307604674187771341201131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1743472898917028454934841 1307604674187771341201131)
                      ·
                        rfl

theorem cell23_2546551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 3, 3, 5, 2].length) (baseStart_2546551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546551 prefixEnd_2546551 := by exact prefixLift 2546551
  have htrace : WordTrace (prefixWord ++ tailWord_2546551) baseStart_2546551 baseEnd_2546551 := by
    simpa [prefixWord, tailWord_2546551, baseEnd_2546551] using wordTrace_append hprefix tailTrace_2546551
  have hstable : (prefixWord ++ tailWord_2546551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546551).length < 2 ^ (prefixWord ++ tailWord_2546551).sum := by decide
  have hdescent : baseEnd_2546551 < baseStart_2546551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546582 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 6]
def baseStart_2546582 : Nat := 118140960795 + 2546582 * 2 ^ 59
def prefixEnd_2546582 : Nat := 4983230072969 + 3 ^ 40 * 2546582 * 2
def baseEnd_2546582 : Nat := 145291176898673413323721

theorem tailTrace_2546582 : CollatzResearch.WordTrace tailWord_2546582 prefixEnd_2546582 145291176898673413323721 := by
  unfold tailWord_2546582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5805092253760988151552125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61920984040117206949889333 5805092253760988151552125)
  ·
    refine ⟨2176909595160370556832047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5805092253760988151552125 2176909595160370556832047)
    ·
      refine ⟨3265364392740555835248071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2176909595160370556832047 3265364392740555835248071)
      ·
        refine ⟨4898046589110833752872107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3265364392740555835248071 4898046589110833752872107)
        ·
          refine ⟨7347069883666250629308161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4898046589110833752872107 7347069883666250629308161)
          ·
            refine ⟨5510302412749687971981121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7347069883666250629308161 5510302412749687971981121)
            ·
              refine ⟨4132726809562265978985841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5510302412749687971981121 4132726809562265978985841)
              ·
                refine ⟨3099545107171699484239381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4132726809562265978985841 3099545107171699484239381)
                ·
                  refine ⟨145291176898673413323721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3099545107171699484239381 145291176898673413323721)
                  ·
                    rfl

theorem cell23_2546582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_2546582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546582 prefixEnd_2546582 := by exact prefixLift 2546582
  have htrace : WordTrace (prefixWord ++ tailWord_2546582) baseStart_2546582 baseEnd_2546582 := by
    simpa [prefixWord, tailWord_2546582, baseEnd_2546582] using wordTrace_append hprefix tailTrace_2546582
  have hstable : (prefixWord ++ tailWord_2546582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546582).length < 2 ^ (prefixWord ++ tailWord_2546582).sum := by decide
  have hdescent : baseEnd_2546582 < baseStart_2546582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546592 : List Nat := [2, 1, 1, 4, 1, 1, 6, 2, 1, 1, 3]
def baseStart_2546592 : Nat := 118140960795 + 2546592 * 2 ^ 59
def prefixEnd_2546592 : Nat := 4983230072969 + 3 ^ 40 * 2546592 * 2
def baseEnd_2546592 : Nat := 1307625726894605680788443

theorem tailTrace_2546592 : CollatzResearch.WordTrace tailWord_2546592 prefixEnd_2546592 1307625726894605680788443 := by
  unfold tailWord_2546592
  simp only [CollatzResearch.WordTrace]
  refine ⟨46440920395069791066349015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61921227193426388088465353 46440920395069791066349015)
  ·
    refine ⟨69661380592604686599523523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46440920395069791066349015 69661380592604686599523523)
    ·
      refine ⟨104492070888907029899285285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69661380592604686599523523 104492070888907029899285285)
      ·
        refine ⟨19592263291670068106115991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104492070888907029899285285 19592263291670068106115991)
        ·
          refine ⟨29388394937505102159173987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19592263291670068106115991 29388394937505102159173987)
          ·
            refine ⟨44082592406257653238760981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29388394937505102159173987 44082592406257653238760981)
            ·
              refine ⟨2066371519043327495566921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44082592406257653238760981 2066371519043327495566921)
              ·
                refine ⟨1549778639282495621675191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2066371519043327495566921 1549778639282495621675191)
                ·
                  refine ⟨2324667958923743432512787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549778639282495621675191 2324667958923743432512787)
                  ·
                    refine ⟨3487001938385615148769181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2324667958923743432512787 3487001938385615148769181)
                    ·
                      refine ⟨1307625726894605680788443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3487001938385615148769181 1307625726894605680788443)
                      ·
                        rfl

theorem cell23_2546592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 6, 2, 1, 1, 3].length) (baseStart_2546592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546592 prefixEnd_2546592 := by exact prefixLift 2546592
  have htrace : WordTrace (prefixWord ++ tailWord_2546592) baseStart_2546592 baseEnd_2546592 := by
    simpa [prefixWord, tailWord_2546592, baseEnd_2546592] using wordTrace_append hprefix tailTrace_2546592
  have hstable : (prefixWord ++ tailWord_2546592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546592).length < 2 ^ (prefixWord ++ tailWord_2546592).sum := by decide
  have hdescent : baseEnd_2546592 < baseStart_2546592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546601 : List Nat := [1, 2, 1, 1, 1, 1, 5, 1, 5, 2, 3]
def baseStart_2546601 : Nat := 118140960795 + 2546601 * 2 ^ 59
def prefixEnd_2546601 : Nat := 4983230072969 + 3 ^ 40 * 2546601 * 2
def baseEnd_2546601 : Nat := 1307630348220496145575901

theorem tailTrace_2546601 : CollatzResearch.WordTrace tailWord_2546601 prefixEnd_2546601 1307630348220496145575901 := by
  unfold tailWord_2546601
  simp only [CollatzResearch.WordTrace]
  refine ⟨92882169047106976669775657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61921446031404651113183771 92882169047106976669775657)
  ·
    refine ⟨69661626785330232502331743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92882169047106976669775657 69661626785330232502331743)
    ·
      refine ⟨104492440177995348753497615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69661626785330232502331743 104492440177995348753497615)
      ·
        refine ⟨156738660266993023130246423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104492440177995348753497615 156738660266993023130246423)
        ·
          refine ⟨235107990400489534695369635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156738660266993023130246423 235107990400489534695369635)
          ·
            refine ⟨352661985600734302043054453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235107990400489534695369635 352661985600734302043054453)
            ·
              refine ⟨33062061150068840816536355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 352661985600734302043054453 33062061150068840816536355)
              ·
                refine ⟨49593091725103261224804533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33062061150068840816536355 49593091725103261224804533)
                ·
                  refine ⟨4649352349228430739825425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49593091725103261224804533 4649352349228430739825425)
                  ·
                    refine ⟨3487014261921323054869069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4649352349228430739825425 3487014261921323054869069)
                    ·
                      refine ⟨1307630348220496145575901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3487014261921323054869069 1307630348220496145575901)
                      ·
                        rfl

theorem cell23_2546601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 1, 5, 2, 3].length) (baseStart_2546601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546601 prefixEnd_2546601 := by exact prefixLift 2546601
  have htrace : WordTrace (prefixWord ++ tailWord_2546601) baseStart_2546601 baseEnd_2546601 := by
    simpa [prefixWord, tailWord_2546601, baseEnd_2546601] using wordTrace_append hprefix tailTrace_2546601
  have hstable : (prefixWord ++ tailWord_2546601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546601).length < 2 ^ (prefixWord ++ tailWord_2546601).sum := by decide
  have hdescent : baseEnd_2546601 < baseStart_2546601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546618 : List Nat := [3, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3]
def baseStart_2546618 : Nat := 118140960795 + 2546618 * 2 ^ 59
def prefixEnd_2546618 : Nat := 4983230072969 + 3 ^ 40 * 2546618 * 2
def baseEnd_2546618 : Nat := 1307639077391622579063323

theorem tailTrace_2546618 : CollatzResearch.WordTrace tailWord_2546618 prefixEnd_2546618 1307639077391622579063323 := by
  unfold tailWord_2546618
  simp only [CollatzResearch.WordTrace]
  refine ⟨23220697272011347143286127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61921859392030259048763005 23220697272011347143286127)
  ·
    refine ⟨34831045908017020714929191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23220697272011347143286127 34831045908017020714929191)
    ·
      refine ⟨52246568862025531072393787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34831045908017020714929191 52246568862025531072393787)
      ·
        refine ⟨78369853293038296608590681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52246568862025531072393787 78369853293038296608590681)
        ·
          refine ⟨58777389969778722456443011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78369853293038296608590681 58777389969778722456443011)
          ·
            refine ⟨88166084954668083684664517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58777389969778722456443011 88166084954668083684664517)
            ·
              refine ⟨16531140929000265690874597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 88166084954668083684664517 16531140929000265690874597)
              ·
                refine ⟨3099588924187549817038987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16531140929000265690874597 3099588924187549817038987)
                ·
                  refine ⟨4649383386281324725558481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099588924187549817038987 4649383386281324725558481)
                  ·
                    refine ⟨3487037539710993544168861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4649383386281324725558481 3487037539710993544168861)
                    ·
                      refine ⟨1307639077391622579063323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3487037539710993544168861 1307639077391622579063323)
                      ·
                        rfl

theorem cell23_2546618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 1, 2, 3].length) (baseStart_2546618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546618 prefixEnd_2546618 := by exact prefixLift 2546618
  have htrace : WordTrace (prefixWord ++ tailWord_2546618) baseStart_2546618 baseEnd_2546618 := by
    simpa [prefixWord, tailWord_2546618, baseEnd_2546618] using wordTrace_append hprefix tailTrace_2546618
  have hstable : (prefixWord ++ tailWord_2546618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546618).length < 2 ^ (prefixWord ++ tailWord_2546618).sum := by decide
  have hdescent : baseEnd_2546618 < baseStart_2546618 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546632 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 1, 1, 4]
def baseStart_2546632 : Nat := 118140960795 + 2546632 * 2 ^ 59
def prefixEnd_2546632 : Nat := 4983230072969 + 3 ^ 40 * 2546632 * 2
def baseEnd_2546632 : Nat := 1307646266120785524288259

theorem tailTrace_2546632 : CollatzResearch.WordTrace tailWord_2546632 prefixEnd_2546632 1307646266120785524288259 := by
  unfold tailWord_2546632
  simp only [CollatzResearch.WordTrace]
  refine ⟨46441649854997334482077075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61922199806663112642769433 46441649854997334482077075)
  ·
    refine ⟨69662474782496001723115613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46441649854997334482077075 69662474782496001723115613)
    ·
      refine ⟨26123428043436000646168355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69662474782496001723115613 26123428043436000646168355)
      ·
        refine ⟨39185142065154000969252533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26123428043436000646168355 39185142065154000969252533)
        ·
          refine ⟨3673607068608187590867425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 39185142065154000969252533 3673607068608187590867425)
          ·
            refine ⟨2755205301456140693150569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3673607068608187590867425 2755205301456140693150569)
            ·
              refine ⟨2066403976092105519862927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755205301456140693150569 2066403976092105519862927)
              ·
                refine ⟨3099605964138158279794391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066403976092105519862927 3099605964138158279794391)
                ·
                  refine ⟨4649408946207237419691587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099605964138158279794391 4649408946207237419691587)
                  ·
                    refine ⟨6974113419310856129537381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4649408946207237419691587 6974113419310856129537381)
                    ·
                      refine ⟨1307646266120785524288259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6974113419310856129537381 1307646266120785524288259)
                      ·
                        rfl

theorem cell23_2546632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 1, 4].length) (baseStart_2546632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546632 prefixEnd_2546632 := by exact prefixLift 2546632
  have htrace : WordTrace (prefixWord ++ tailWord_2546632) baseStart_2546632 baseEnd_2546632 := by
    simpa [prefixWord, tailWord_2546632, baseEnd_2546632] using wordTrace_append hprefix tailTrace_2546632
  have hstable : (prefixWord ++ tailWord_2546632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546632).length < 2 ^ (prefixWord ++ tailWord_2546632).sum := by decide
  have hdescent : baseEnd_2546632 < baseStart_2546632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546635 : List Nat := [1, 1, 1, 1, 3, 5, 4, 1, 1, 2, 3]
def baseStart_2546635 : Nat := 118140960795 + 2546635 * 2 ^ 59
def prefixEnd_2546635 : Nat := 4983230072969 + 3 ^ 40 * 2546635 * 2
def baseEnd_2546635 : Nat := 1307647806562749012550745

theorem tailTrace_2546635 : CollatzResearch.WordTrace tailWord_2546635 prefixEnd_2546635 1307647806562749012550745 := by
  unfold tailWord_2546635
  simp only [CollatzResearch.WordTrace]
  refine ⟨92883409128983800476513359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61922272752655866984342239 92883409128983800476513359)
  ·
    refine ⟨139325113693475700714770039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92883409128983800476513359 139325113693475700714770039)
    ·
      refine ⟨208987670540213551072155059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139325113693475700714770039 208987670540213551072155059)
      ·
        refine ⟨313481505810320326608232589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208987670540213551072155059 313481505810320326608232589)
        ·
          refine ⟨117555564678870122478087221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 313481505810320326608232589 117555564678870122478087221)
          ·
            refine ⟨11020834188644073982320677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117555564678870122478087221 11020834188644073982320677)
            ·
              refine ⟨2066406410370763871685127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11020834188644073982320677 2066406410370763871685127)
              ·
                refine ⟨3099609615556145807527691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066406410370763871685127 3099609615556145807527691)
                ·
                  refine ⟨4649414423334218711291537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3099609615556145807527691 4649414423334218711291537)
                  ·
                    refine ⟨3487060817500664033468653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4649414423334218711291537 3487060817500664033468653)
                    ·
                      refine ⟨1307647806562749012550745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3487060817500664033468653 1307647806562749012550745)
                      ·
                        rfl

theorem cell23_2546635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 4, 1, 1, 2, 3].length) (baseStart_2546635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546635 prefixEnd_2546635 := by exact prefixLift 2546635
  have htrace : WordTrace (prefixWord ++ tailWord_2546635) baseStart_2546635 baseEnd_2546635 := by
    simpa [prefixWord, tailWord_2546635, baseEnd_2546635] using wordTrace_append hprefix tailTrace_2546635
  have hstable : (prefixWord ++ tailWord_2546635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546635).length < 2 ^ (prefixWord ++ tailWord_2546635).sum := by decide
  have hdescent : baseEnd_2546635 < baseStart_2546635 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546642 : List Nat := [3, 2, 2, 3, 1, 3, 1, 2, 2, 4]
def baseStart_2546642 : Nat := 118140960795 + 2546642 * 2 ^ 59
def prefixEnd_2546642 : Nat := 4983230072969 + 3 ^ 40 * 2546642 * 2
def baseEnd_2546642 : Nat := 435883800309110161721071

theorem tailTrace_2546642 : CollatzResearch.WordTrace tailWord_2546642 prefixEnd_2546642 435883800309110161721071 := by
  unfold tailWord_2546642
  simp only [CollatzResearch.WordTrace]
  refine ⟨23220916109989610168004545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61922442959972293781345453 23220916109989610168004545)
  ·
    refine ⟨17415687082492207626003409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23220916109989610168004545 17415687082492207626003409)
    ·
      refine ⟨13061765311869155719502557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17415687082492207626003409 13061765311869155719502557)
      ·
        refine ⟨4898161991950933394813459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13061765311869155719502557 4898161991950933394813459)
        ·
          refine ⟨7347242987926400092220189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4898161991950933394813459 7347242987926400092220189)
          ·
            refine ⟨2755216120472400034582571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7347242987926400092220189 2755216120472400034582571)
            ·
              refine ⟨4132824180708600051873857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755216120472400034582571 4132824180708600051873857)
              ·
                refine ⟨3099618135531450038905393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4132824180708600051873857 3099618135531450038905393)
                ·
                  refine ⟨2324713601648587529179045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3099618135531450038905393 2324713601648587529179045)
                  ·
                    refine ⟨435883800309110161721071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2324713601648587529179045 435883800309110161721071)
                    ·
                      rfl

theorem cell23_2546642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_2546642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546642 prefixEnd_2546642 := by exact prefixLift 2546642
  have htrace : WordTrace (prefixWord ++ tailWord_2546642) baseStart_2546642 baseEnd_2546642 := by
    simpa [prefixWord, tailWord_2546642, baseEnd_2546642] using wordTrace_append hprefix tailTrace_2546642
  have hstable : (prefixWord ++ tailWord_2546642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546642).length < 2 ^ (prefixWord ++ tailWord_2546642).sum := by decide
  have hdescent : baseEnd_2546642 < baseStart_2546642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546678 : List Nat := [5, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5]
def baseStart_2546678 : Nat := 118140960795 + 2546678 * 2 ^ 59
def prefixEnd_2546678 : Nat := 4983230072969 + 3 ^ 40 * 2546678 * 2
def baseEnd_2546678 : Nat := 1307669886230892344313047

theorem tailTrace_2546678 : CollatzResearch.WordTrace tailWord_2546678 prefixEnd_2546678 1307669886230892344313047 := by
  unfold tailWord_2546678
  simp only [CollatzResearch.WordTrace]
  refine ⟨5805311091739251176270543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 61923318311885345880219125 5805311091739251176270543)
  ·
    refine ⟨8707966637608876764405815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5805311091739251176270543 8707966637608876764405815)
    ·
      refine ⟨13061949956413315146608723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8707966637608876764405815 13061949956413315146608723)
      ·
        refine ⟨19592924934619972719913085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13061949956413315146608723 19592924934619972719913085)
        ·
          refine ⟨7347346850482489769967407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19592924934619972719913085 7347346850482489769967407)
          ·
            refine ⟨11021020275723734654951111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7347346850482489769967407 11021020275723734654951111)
            ·
              refine ⟨16531530413585601982426667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11021020275723734654951111 16531530413585601982426667)
              ·
                refine ⟨24797295620378402973640001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16531530413585601982426667 24797295620378402973640001)
                ·
                  refine ⟨18597971715283802230230001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24797295620378402973640001 18597971715283802230230001)
                  ·
                    refine ⟨13948478786462851672672501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18597971715283802230230001 13948478786462851672672501)
                    ·
                      refine ⟨1307669886230892344313047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13948478786462851672672501 1307669886230892344313047)
                      ·
                        rfl

theorem cell23_2546678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 1, 2, 2, 5].length) (baseStart_2546678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546678 prefixEnd_2546678 := by exact prefixLift 2546678
  have htrace : WordTrace (prefixWord ++ tailWord_2546678) baseStart_2546678 baseEnd_2546678 := by
    simpa [prefixWord, tailWord_2546678, baseEnd_2546678] using wordTrace_append hprefix tailTrace_2546678
  have hstable : (prefixWord ++ tailWord_2546678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546678).length < 2 ^ (prefixWord ++ tailWord_2546678).sum := by decide
  have hdescent : baseEnd_2546678 < baseStart_2546678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546691 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 3]
def baseStart_2546691 : Nat := 118140960795 + 2546691 * 2 ^ 59
def prefixEnd_2546691 : Nat := 4983230072969 + 3 ^ 40 * 2546691 * 2
def baseEnd_2546691 : Nat := 1307676561479400793450487

theorem tailTrace_2546691 : CollatzResearch.WordTrace tailWord_2546691 prefixEnd_2546691 1307676561479400793450487 := by
  unfold tailWord_2546691
  simp only [CollatzResearch.WordTrace]
  refine ⟨92885451616780922040551927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61923634411187281360367951 92885451616780922040551927)
  ·
    refine ⟨139328177425171383060827891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92885451616780922040551927 139328177425171383060827891)
    ·
      refine ⟨208992266137757074591241837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139328177425171383060827891 208992266137757074591241837)
      ·
        refine ⟨78372099801658902971715689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 208992266137757074591241837 78372099801658902971715689)
        ·
          refine ⟨58779074851244177228786767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78372099801658902971715689 58779074851244177228786767)
          ·
            refine ⟨88168612276866265843180151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58779074851244177228786767 88168612276866265843180151)
            ·
              refine ⟨132252918415299398764770227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88168612276866265843180151 132252918415299398764770227)
              ·
                refine ⟨198379377622949098147155341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132252918415299398764770227 198379377622949098147155341)
                ·
                  refine ⟨74392266608605911805183253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 198379377622949098147155341 74392266608605911805183253)
                  ·
                    refine ⟨3487137497278402115867965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 74392266608605911805183253 3487137497278402115867965)
                    ·
                      refine ⟨1307676561479400793450487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3487137497278402115867965 1307676561479400793450487)
                      ·
                        rfl

theorem cell23_2546691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 3, 6, 3].length) (baseStart_2546691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546691 prefixEnd_2546691 := by exact prefixLift 2546691
  have htrace : WordTrace (prefixWord ++ tailWord_2546691) baseStart_2546691 baseEnd_2546691 := by
    simpa [prefixWord, tailWord_2546691, baseEnd_2546691] using wordTrace_append hprefix tailTrace_2546691
  have hstable : (prefixWord ++ tailWord_2546691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546691).length < 2 ^ (prefixWord ++ tailWord_2546691).sum := by decide
  have hdescent : baseEnd_2546691 < baseStart_2546691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546716 : List Nat := [2, 2, 3, 1, 5, 1, 2, 1, 2, 1, 3]
def baseStart_2546716 : Nat := 118140960795 + 2546716 * 2 ^ 59
def prefixEnd_2546716 : Nat := 4983230072969 + 3 ^ 40 * 2546716 * 2
def baseEnd_2546716 : Nat := 1307689398495763195637873

theorem tailTrace_2546716 : CollatzResearch.WordTrace tailWord_2546716 prefixEnd_2546716 1307689398495763195637873 := by
  unfold tailWord_2546716
  simp only [CollatzResearch.WordTrace]
  refine ⟨46443181720845175655106001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61924242294460234206808001 46443181720845175655106001)
  ·
    refine ⟨34832386290633881741329501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46443181720845175655106001 34832386290633881741329501)
    ·
      refine ⟨13062144858987705652998563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34832386290633881741329501 13062144858987705652998563)
      ·
        refine ⟨19593217288481558479497845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13062144858987705652998563 19593217288481558479497845)
        ·
          refine ⟨1836864120795146107452923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19593217288481558479497845 1836864120795146107452923)
          ·
            refine ⟨2755296181192719161179385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1836864120795146107452923 2755296181192719161179385)
            ·
              refine ⟨2066472135894539370884539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755296181192719161179385 2066472135894539370884539)
              ·
                refine ⟨3099708203841809056326809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066472135894539370884539 3099708203841809056326809)
                ·
                  refine ⟨2324781152881356792245107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3099708203841809056326809 2324781152881356792245107)
                  ·
                    refine ⟨3487171729322035188367661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2324781152881356792245107 3487171729322035188367661)
                    ·
                      refine ⟨1307689398495763195637873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3487171729322035188367661 1307689398495763195637873)
                      ·
                        rfl

theorem cell23_2546716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_2546716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546716 prefixEnd_2546716 := by exact prefixLift 2546716
  have htrace : WordTrace (prefixWord ++ tailWord_2546716) baseStart_2546716 baseEnd_2546716 := by
    simpa [prefixWord, tailWord_2546716, baseEnd_2546716] using wordTrace_append hprefix tailTrace_2546716
  have hstable : (prefixWord ++ tailWord_2546716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546716).length < 2 ^ (prefixWord ++ tailWord_2546716).sum := by decide
  have hdescent : baseEnd_2546716 < baseStart_2546716 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546886 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 6]
def baseStart_2546886 : Nat := 118140960795 + 2546886 * 2 ^ 59
def prefixEnd_2546886 : Nat := 4983230072969 + 3 ^ 40 * 2546886 * 2
def baseEnd_2546886 : Nat := 145308521134114170056899

theorem tailTrace_2546886 : CollatzResearch.WordTrace tailWord_2546886 prefixEnd_2546886 145308521134114170056899 := by
  unfold tailWord_2546886
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902892620346077198246891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 61928375900716313562600341 2902892620346077198246891)
  ·
    refine ⟨4354338930519115797370337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2902892620346077198246891 4354338930519115797370337)
    ·
      refine ⟨3265754197889336848027753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4354338930519115797370337 3265754197889336848027753)
      ·
        refine ⟨2449315648417002636020815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3265754197889336848027753 2449315648417002636020815)
        ·
          refine ⟨3673973472625503954031223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2449315648417002636020815 3673973472625503954031223)
          ·
            refine ⟨5510960208938255931046835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3673973472625503954031223 5510960208938255931046835)
            ·
              refine ⟨8266440313407383896570253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5510960208938255931046835 8266440313407383896570253)
              ·
                refine ⟨3099915117527768961213845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8266440313407383896570253 3099915117527768961213845)
                ·
                  refine ⟨145308521134114170056899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3099915117527768961213845 145308521134114170056899)
                  ·
                    rfl

theorem cell23_2546886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_2546886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546886 prefixEnd_2546886 := by exact prefixLift 2546886
  have htrace : WordTrace (prefixWord ++ tailWord_2546886) baseStart_2546886 baseEnd_2546886 := by
    simpa [prefixWord, tailWord_2546886, baseEnd_2546886] using wordTrace_append hprefix tailTrace_2546886
  have hstable : (prefixWord ++ tailWord_2546886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546886).length < 2 ^ (prefixWord ++ tailWord_2546886).sum := by decide
  have hdescent : baseEnd_2546886 < baseStart_2546886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546922 : List Nat := [3, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_2546922 : Nat := 118140960795 + 2546922 * 2 ^ 59
def prefixEnd_2546922 : Nat := 4983230072969 + 3 ^ 40 * 2546922 * 2
def baseEnd_2546922 : Nat := 1307795175510589389661925

theorem tailTrace_2546922 : CollatzResearch.WordTrace tailWord_2546922 prefixEnd_2546922 1307795175510589389661925 := by
  unfold tailWord_2546922
  simp only [CollatzResearch.WordTrace]
  refine ⟨23223469219736012123052755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61929251252629365661474013 23223469219736012123052755)
  ·
    refine ⟨34835203829604018184579133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23223469219736012123052755 34835203829604018184579133)
    ·
      refine ⟨13063201436101506819217175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34835203829604018184579133 13063201436101506819217175)
      ·
        refine ⟨19594802154152260228825763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13063201436101506819217175 19594802154152260228825763)
        ·
          refine ⟨29392203231228390343238645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19594802154152260228825763 29392203231228390343238645)
          ·
            refine ⟨2755519052927661594678623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 29392203231228390343238645 2755519052927661594678623)
            ·
              refine ⟨4133278579391492392017935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755519052927661594678623 4133278579391492392017935)
              ·
                refine ⟨6199917869087238588026903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4133278579391492392017935 6199917869087238588026903)
                ·
                  refine ⟨9299876803630857882040355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6199917869087238588026903 9299876803630857882040355)
                  ·
                    refine ⟨13949815205446286823060533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9299876803630857882040355 13949815205446286823060533)
                    ·
                      refine ⟨1307795175510589389661925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13949815205446286823060533 1307795175510589389661925)
                      ·
                        rfl

theorem cell23_2546922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_2546922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546922 prefixEnd_2546922 := by exact prefixLift 2546922
  have htrace : WordTrace (prefixWord ++ tailWord_2546922) baseStart_2546922 baseEnd_2546922 := by
    simpa [prefixWord, tailWord_2546922, baseEnd_2546922] using wordTrace_append hprefix tailTrace_2546922
  have hstable : (prefixWord ++ tailWord_2546922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546922).length < 2 ^ (prefixWord ++ tailWord_2546922).sum := by decide
  have hdescent : baseEnd_2546922 < baseStart_2546922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546930 : List Nat := [3, 2, 1, 3, 4, 1, 2, 2, 1, 1, 3]
def baseStart_2546930 : Nat := 118140960795 + 2546930 * 2 ^ 59
def prefixEnd_2546930 : Nat := 4983230072969 + 3 ^ 40 * 2546930 * 2
def baseEnd_2546930 : Nat := 1307799283355825358361889

theorem tailTrace_2546930 : CollatzResearch.WordTrace tailWord_2546930 prefixEnd_2546930 1307799283355825358361889 := by
  unfold tailWord_2546930
  simp only [CollatzResearch.WordTrace]
  refine ⟨23223542165728766464625561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61929445775276710572334829 23223542165728766464625561)
  ·
    refine ⟨17417656624296574848469171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23223542165728766464625561 17417656624296574848469171)
    ·
      refine ⟨26126484936444862272703757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17417656624296574848469171 26126484936444862272703757)
      ·
        refine ⟨9797431851166823352263909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26126484936444862272703757 9797431851166823352263909)
        ·
          refine ⟨1837018472093779378549483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9797431851166823352263909 1837018472093779378549483)
          ·
            refine ⟨2755527708140669067824225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837018472093779378549483 2755527708140669067824225)
            ·
              refine ⟨2066645781105501800868169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755527708140669067824225 2066645781105501800868169)
              ·
                refine ⟨1549984335829126350651127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2066645781105501800868169 1549984335829126350651127)
                ·
                  refine ⟨2324976503743689525976691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1549984335829126350651127 2324976503743689525976691)
                  ·
                    refine ⟨3487464755615534288965037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2324976503743689525976691 3487464755615534288965037)
                    ·
                      refine ⟨1307799283355825358361889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3487464755615534288965037 1307799283355825358361889)
                      ·
                        rfl

theorem cell23_2546930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 2, 2, 1, 1, 3].length) (baseStart_2546930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546930 prefixEnd_2546930 := by exact prefixLift 2546930
  have htrace : WordTrace (prefixWord ++ tailWord_2546930) baseStart_2546930 baseEnd_2546930 := by
    simpa [prefixWord, tailWord_2546930, baseEnd_2546930] using wordTrace_append hprefix tailTrace_2546930
  have hstable : (prefixWord ++ tailWord_2546930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546930).length < 2 ^ (prefixWord ++ tailWord_2546930).sum := by decide
  have hdescent : baseEnd_2546930 < baseStart_2546930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546938 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 1, 9]
def baseStart_2546938 : Nat := 118140960795 + 2546938 * 2 ^ 59
def prefixEnd_2546938 : Nat := 4983230072969 + 3 ^ 40 * 2546938 * 2
def baseEnd_2546938 : Nat := 435934463733687109020617

theorem tailTrace_2546938 : CollatzResearch.WordTrace tailWord_2546938 prefixEnd_2546938 435934463733687109020617 := by
  unfold tailWord_2546938
  simp only [CollatzResearch.WordTrace]
  refine ⟨23223615111721520806198367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61929640297924055483195645 23223615111721520806198367)
  ·
    refine ⟨34835422667582281209297551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23223615111721520806198367 34835422667582281209297551)
    ·
      refine ⟨52253134001373421813946327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34835422667582281209297551 52253134001373421813946327)
      ·
        refine ⟨78379701002060132720919491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52253134001373421813946327 78379701002060132720919491)
        ·
          refine ⟨117569551503090199081379237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78379701002060132720919491 117569551503090199081379237)
          ·
            refine ⟨22044290906829412327758607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117569551503090199081379237 22044290906829412327758607)
            ·
              refine ⟨33066436360244118491637911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22044290906829412327758607 33066436360244118491637911)
              ·
                refine ⟨49599654540366177737456867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33066436360244118491637911 49599654540366177737456867)
                ·
                  refine ⟨74399481810549266606185301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 49599654540366177737456867 74399481810549266606185301)
                  ·
                    refine ⟨435934463733687109020617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 74399481810549266606185301 435934463733687109020617)
                    ·
                      rfl

theorem cell23_2546938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_2546938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546938 prefixEnd_2546938 := by exact prefixLift 2546938
  have htrace : WordTrace (prefixWord ++ tailWord_2546938) baseStart_2546938 baseEnd_2546938 := by
    simpa [prefixWord, tailWord_2546938, baseEnd_2546938] using wordTrace_append hprefix tailTrace_2546938
  have hstable : (prefixWord ++ tailWord_2546938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546938).length < 2 ^ (prefixWord ++ tailWord_2546938).sum := by decide
  have hdescent : baseEnd_2546938 < baseStart_2546938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546942 : List Nat := [4, 2, 2, 1, 1, 4, 1, 8]
def baseStart_2546942 : Nat := 118140960795 + 2546942 * 2 ^ 59
def prefixEnd_2546942 : Nat := 4983230072969 + 3 ^ 40 * 2546942 * 2
def baseEnd_2546942 : Nat := 48437238708284418941179

theorem tailTrace_2546942 : CollatzResearch.WordTrace tailWord_2546942 prefixEnd_2546942 48437238708284418941179 := by
  unfold tailWord_2546942
  simp only [CollatzResearch.WordTrace]
  refine ⟨11611825792358948988492385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61929737559247727938626053 11611825792358948988492385)
  ·
    refine ⟨8708869344269211741369289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11611825792358948988492385 8708869344269211741369289)
    ·
      refine ⟨6531652008201908806026967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8708869344269211741369289 6531652008201908806026967)
      ·
        refine ⟨9797478012302863209040451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6531652008201908806026967 9797478012302863209040451)
        ·
          refine ⟨14696217018454294813560677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9797478012302863209040451 14696217018454294813560677)
          ·
            refine ⟨2755540690960180277542627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14696217018454294813560677 2755540690960180277542627)
            ·
              refine ⟨4133311036440270416313941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755540690960180277542627 4133311036440270416313941)
              ·
                refine ⟨48437238708284418941179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4133311036440270416313941 48437238708284418941179)
                ·
                  rfl

theorem cell23_2546942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 1, 8].length) (baseStart_2546942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546942 prefixEnd_2546942 := by exact prefixLift 2546942
  have htrace : WordTrace (prefixWord ++ tailWord_2546942) baseStart_2546942 baseEnd_2546942 := by
    simpa [prefixWord, tailWord_2546942, baseEnd_2546942] using wordTrace_append hprefix tailTrace_2546942
  have hstable : (prefixWord ++ tailWord_2546942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546942).length < 2 ^ (prefixWord ++ tailWord_2546942).sum := by decide
  have hdescent : baseEnd_2546942 < baseStart_2546942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546979 : List Nat := [1, 1, 1, 4, 2, 4, 1, 3, 1, 3, 2]
def baseStart_2546979 : Nat := 118140960795 + 2546979 * 2 ^ 59
def prefixEnd_2546979 : Nat := 4983230072969 + 3 ^ 40 * 2546979 * 2
def baseEnd_2546979 : Nat := 1307824443907895666649163

theorem tailTrace_2546979 : CollatzResearch.WordTrace tailWord_2546979 prefixEnd_2546979 1307824443907895666649163 := by
  unfold tailWord_2546979
  simp only [CollatzResearch.WordTrace]
  refine ⟨92895955839737547227035991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61930637226491698151357327 92895955839737547227035991)
  ·
    refine ⟨139343933759606320840553987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92895955839737547227035991 139343933759606320840553987)
    ·
      refine ⟨209015900639409481260830981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139343933759606320840553987 209015900639409481260830981)
      ·
        refine ⟨39190481369889277736405809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 209015900639409481260830981 39190481369889277736405809)
        ·
          refine ⟨29392861027416958302304357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39190481369889277736405809 29392861027416958302304357)
          ·
            refine ⟨5511161442640679681682067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29392861027416958302304357 5511161442640679681682067)
            ·
              refine ⟨8266742163961019522523101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5511161442640679681682067 8266742163961019522523101)
              ·
                refine ⟨3100028311485382320946163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8266742163961019522523101 3100028311485382320946163)
                ·
                  refine ⟨4650042467228073481419245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100028311485382320946163 4650042467228073481419245)
                  ·
                    refine ⟨1743765925210527555532217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4650042467228073481419245 1743765925210527555532217)
                    ·
                      refine ⟨1307824443907895666649163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1743765925210527555532217 1307824443907895666649163)
                      ·
                        rfl

theorem cell23_2546979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_2546979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546979 prefixEnd_2546979 := by exact prefixLift 2546979
  have htrace : WordTrace (prefixWord ++ tailWord_2546979) baseStart_2546979 baseEnd_2546979 := by
    simpa [prefixWord, tailWord_2546979, baseEnd_2546979] using wordTrace_append hprefix tailTrace_2546979
  have hstable : (prefixWord ++ tailWord_2546979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546979).length < 2 ^ (prefixWord ++ tailWord_2546979).sum := by decide
  have hdescent : baseEnd_2546979 < baseStart_2546979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2546986 : List Nat := [3, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_2546986 : Nat := 118140960795 + 2546986 * 2 ^ 59
def prefixEnd_2546986 : Nat := 4983230072969 + 3 ^ 40 * 2546986 * 2
def baseEnd_2546986 : Nat := 1307828038272477139261631

theorem tailTrace_2546986 : CollatzResearch.WordTrace tailWord_2546986 prefixEnd_2546986 1307828038272477139261631 := by
  unfold tailWord_2546986
  simp only [CollatzResearch.WordTrace]
  refine ⟨23224052787678046855635203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61930807433808124948360541 23224052787678046855635203)
  ·
    refine ⟨34836079181517070283452805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23224052787678046855635203 34836079181517070283452805)
    ·
      refine ⟨6531764846534450678147401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34836079181517070283452805 6531764846534450678147401)
      ·
        refine ⟨4898823634900838008610551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6531764846534450678147401 4898823634900838008610551)
        ·
          refine ⟨7348235452351257012915827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4898823634900838008610551 7348235452351257012915827)
          ·
            refine ⟨11022353178526885519373741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7348235452351257012915827 11022353178526885519373741)
            ·
              refine ⟨4133382441947582069765153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11022353178526885519373741 4133382441947582069765153)
              ·
                refine ⟨3100036831460686552323865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4133382441947582069765153 3100036831460686552323865)
                ·
                  refine ⟨2325027623595514914242899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3100036831460686552323865 2325027623595514914242899)
                  ·
                    refine ⟨3487541435393272371364349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2325027623595514914242899 3487541435393272371364349)
                    ·
                      refine ⟨1307828038272477139261631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3487541435393272371364349 1307828038272477139261631)
                      ·
                        rfl

theorem cell23_2546986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_2546986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2546986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2546986 prefixEnd_2546986 := by exact prefixLift 2546986
  have htrace : WordTrace (prefixWord ++ tailWord_2546986) baseStart_2546986 baseEnd_2546986 := by
    simpa [prefixWord, tailWord_2546986, baseEnd_2546986] using wordTrace_append hprefix tailTrace_2546986
  have hstable : (prefixWord ++ tailWord_2546986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2546986).length < 2 ^ (prefixWord ++ tailWord_2546986).sum := by decide
  have hdescent : baseEnd_2546986 < baseStart_2546986 := by decide
  rcases family_descends (prefixWord ++ tailWord_2546986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547015 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 7]
def baseStart_2547015 : Nat := 118140960795 + 2547015 * 2 ^ 59
def prefixEnd_2547015 : Nat := 4983230072969 + 3 ^ 40 * 2547015 * 2
def baseEnd_2547015 : Nat := 145315881023495280644333

theorem tailTrace_2547015 : CollatzResearch.WordTrace tailWord_2547015 prefixEnd_2547015 145315881023495280644333 := by
  unfold tailWord_2547015
  simp only [CollatzResearch.WordTrace]
  refine ⟨92897268867607125375346499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61931512578404750250230999 92897268867607125375346499)
  ·
    refine ⟨139345903301410688063019749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92897268867607125375346499 139345903301410688063019749)
    ·
      refine ⟨26127356869014504011816203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 139345903301410688063019749 26127356869014504011816203)
      ·
        refine ⟨39191035303521756017724305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26127356869014504011816203 39191035303521756017724305)
        ·
          refine ⟨29393276477641317013293229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39191035303521756017724305 29393276477641317013293229)
          ·
            refine ⟨11022478679115493879984961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 29393276477641317013293229 11022478679115493879984961)
            ·
              refine ⟨8266859009336620409988721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11022478679115493879984961 8266859009336620409988721)
              ·
                refine ⟨6200144257002465307491541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8266859009336620409988721 6200144257002465307491541)
                ·
                  refine ⟨145315881023495280644333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6200144257002465307491541 145315881023495280644333)
                  ·
                    rfl

theorem cell23_2547015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 7].length) (baseStart_2547015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547015 prefixEnd_2547015 := by exact prefixLift 2547015
  have htrace : WordTrace (prefixWord ++ tailWord_2547015) baseStart_2547015 baseEnd_2547015 := by
    simpa [prefixWord, tailWord_2547015, baseEnd_2547015] using wordTrace_append hprefix tailTrace_2547015
  have hstable : (prefixWord ++ tailWord_2547015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547015).length < 2 ^ (prefixWord ++ tailWord_2547015).sum := by decide
  have hdescent : baseEnd_2547015 < baseStart_2547015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547055 : List Nat := [1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 5]
def baseStart_2547055 : Nat := 118140960795 + 2547055 * 2 ^ 59
def prefixEnd_2547055 : Nat := 4983230072969 + 3 ^ 40 * 2547055 * 2
def baseEnd_2547055 : Nat := 1307863468437637369298813

theorem tailTrace_2547055 : CollatzResearch.WordTrace tailWord_2547055 prefixEnd_2547055 1307863468437637369298813 := by
  unfold tailWord_2547055
  simp only [CollatzResearch.WordTrace]
  refine ⟨92898727787462212206802619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61932485191641474804535079 92898727787462212206802619)
  ·
    refine ⟨139348091681193318310203929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92898727787462212206802619 139348091681193318310203929)
    ·
      refine ⟨104511068760894988732652947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139348091681193318310203929 104511068760894988732652947)
      ·
        refine ⟨156766603141342483098979421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104511068760894988732652947 156766603141342483098979421)
        ·
          refine ⟨58787476178003431162117283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156766603141342483098979421 58787476178003431162117283)
          ·
            refine ⟨88181214267005146743175925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58787476178003431162117283 88181214267005146743175925)
            ·
              refine ⟨8266988837531732507172743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 88181214267005146743175925 8266988837531732507172743)
              ·
                refine ⟨12400483256297598760759115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8266988837531732507172743 12400483256297598760759115)
                ·
                  refine ⟨18600724884446398141138673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12400483256297598760759115 18600724884446398141138673)
                  ·
                    refine ⟨13950543663334798605854005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18600724884446398141138673 13950543663334798605854005)
                    ·
                      refine ⟨1307863468437637369298813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13950543663334798605854005 1307863468437637369298813)
                      ·
                        rfl

theorem cell23_2547055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 5].length) (baseStart_2547055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547055 prefixEnd_2547055 := by exact prefixLift 2547055
  have htrace : WordTrace (prefixWord ++ tailWord_2547055) baseStart_2547055 baseEnd_2547055 := by
    simpa [prefixWord, tailWord_2547055, baseEnd_2547055] using wordTrace_append hprefix tailTrace_2547055
  have hstable : (prefixWord ++ tailWord_2547055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547055).length < 2 ^ (prefixWord ++ tailWord_2547055).sum := by decide
  have hdescent : baseEnd_2547055 < baseStart_2547055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547065 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 4]
def baseStart_2547065 : Nat := 118140960795 + 2547065 * 2 ^ 59
def prefixEnd_2547065 : Nat := 4983230072969 + 3 ^ 40 * 2547065 * 2
def baseEnd_2547065 : Nat := 1307868603244182330173767

theorem tailTrace_2547065 : CollatzResearch.WordTrace tailWord_2547065 prefixEnd_2547065 1307868603244182330173767 := by
  unfold tailWord_2547065
  simp only [CollatzResearch.WordTrace]
  refine ⟨92899092517425983914666649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61932728344950655943111099 92899092517425983914666649)
  ·
    refine ⟨69674319388069487935999987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92899092517425983914666649 69674319388069487935999987)
    ·
      refine ⟨104511479082104231903999981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69674319388069487935999987 104511479082104231903999981)
      ·
        refine ⟨39191804655789086963999993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104511479082104231903999981 39191804655789086963999993)
        ·
          refine ⟨29393853491841815222999995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39191804655789086963999993 29393853491841815222999995)
          ·
            refine ⟨44090780237762722834499993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29393853491841815222999995 44090780237762722834499993)
            ·
              refine ⟨33068085178322042125874995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44090780237762722834499993 33068085178322042125874995)
              ·
                refine ⟨49602127767483063188812493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33068085178322042125874995 49602127767483063188812493)
                ·
                  refine ⟨18600797912806148695804685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 49602127767483063188812493 18600797912806148695804685)
                  ·
                    refine ⟨6975299217302305760926757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18600797912806148695804685 6975299217302305760926757)
                    ·
                      refine ⟨1307868603244182330173767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6975299217302305760926757 1307868603244182330173767)
                      ·
                        rfl

theorem cell23_2547065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 3, 4].length) (baseStart_2547065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547065 prefixEnd_2547065 := by exact prefixLift 2547065
  have htrace : WordTrace (prefixWord ++ tailWord_2547065) baseStart_2547065 baseEnd_2547065 := by
    simpa [prefixWord, tailWord_2547065, baseEnd_2547065] using wordTrace_append hprefix tailTrace_2547065
  have hstable : (prefixWord ++ tailWord_2547065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547065).length < 2 ^ (prefixWord ++ tailWord_2547065).sum := by decide
  have hdescent : baseEnd_2547065 < baseStart_2547065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547095 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2547095 : Nat := 118140960795 + 2547095 * 2 ^ 59
def prefixEnd_2547095 : Nat := 4983230072969 + 3 ^ 40 * 2547095 * 2
def baseEnd_2547095 : Nat := 1307884007663817212798629

theorem tailTrace_2547095 : CollatzResearch.WordTrace tailWord_2547095 prefixEnd_2547095 1307884007663817212798629 := by
  unfold tailWord_2547095
  simp only [CollatzResearch.WordTrace]
  refine ⟨92900186707317299038258739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61933457804878199358839159 92900186707317299038258739)
  ·
    refine ⟨139350280060975948557388109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92900186707317299038258739 139350280060975948557388109)
    ·
      refine ⟨52256355022865980709020541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139350280060975948557388109 52256355022865980709020541)
      ·
        refine ⟨19596133133574742765882703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52256355022865980709020541 19596133133574742765882703)
        ·
          refine ⟨29394199700362114148824055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19596133133574742765882703 29394199700362114148824055)
          ·
            refine ⟨44091299550543171223236083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29394199700362114148824055 44091299550543171223236083)
            ·
              refine ⟨66136949325814756834854125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44091299550543171223236083 66136949325814756834854125)
              ·
                refine ⟨24801355997180533813070297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 66136949325814756834854125 24801355997180533813070297)
                ·
                  refine ⟨18601016997885400359802723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24801355997180533813070297 18601016997885400359802723)
                  ·
                    refine ⟨27901525496828100539704085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18601016997885400359802723 27901525496828100539704085)
                    ·
                      refine ⟨1307884007663817212798629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 27901525496828100539704085 1307884007663817212798629)
                      ·
                        rfl

theorem cell23_2547095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2547095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547095 prefixEnd_2547095 := by exact prefixLift 2547095
  have htrace : WordTrace (prefixWord ++ tailWord_2547095) baseStart_2547095 baseEnd_2547095 := by
    simpa [prefixWord, tailWord_2547095, baseEnd_2547095] using wordTrace_append hprefix tailTrace_2547095
  have hstable : (prefixWord ++ tailWord_2547095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547095).length < 2 ^ (prefixWord ++ tailWord_2547095).sum := by decide
  have hdescent : baseEnd_2547095 < baseStart_2547095 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547100 : List Nat := [2, 2, 3, 4, 2, 1, 2, 2, 5]
def baseStart_2547100 : Nat := 118140960795 + 2547100 * 2 ^ 59
def prefixEnd_2547100 : Nat := 4983230072969 + 3 ^ 40 * 2547100 * 2
def baseEnd_2547100 : Nat := 145320730563009965915123

theorem tailTrace_2547100 : CollatzResearch.WordTrace tailWord_2547100 prefixEnd_2547100 145320730563009965915123 := by
  unfold tailWord_2547100
  simp only [CollatzResearch.WordTrace]
  refine ⟨46450184536149592446095377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61933579381532789928127169 46450184536149592446095377)
  ·
    refine ⟨34837638402112194334571533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46450184536149592446095377 34837638402112194334571533)
    ·
      refine ⟨13064114400792072875464325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34837638402112194334571533 13064114400792072875464325)
      ·
        refine ⟨2449521450148513664149561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13064114400792072875464325 2449521450148513664149561)
        ·
          refine ⟨1837141087611385248112171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2449521450148513664149561 1837141087611385248112171)
          ·
            refine ⟨2755711631417077872168257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837141087611385248112171 2755711631417077872168257)
            ·
              refine ⟨2066783723562808404126193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755711631417077872168257 2066783723562808404126193)
              ·
                refine ⟨1550087792672106303094645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2066783723562808404126193 1550087792672106303094645)
                ·
                  refine ⟨145320730563009965915123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1550087792672106303094645 145320730563009965915123)
                  ·
                    rfl

theorem cell23_2547100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 5].length) (baseStart_2547100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547100 prefixEnd_2547100 := by exact prefixLift 2547100
  have htrace : WordTrace (prefixWord ++ tailWord_2547100) baseStart_2547100 baseEnd_2547100 := by
    simpa [prefixWord, tailWord_2547100, baseEnd_2547100] using wordTrace_append hprefix tailTrace_2547100
  have hstable : (prefixWord ++ tailWord_2547100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547100).length < 2 ^ (prefixWord ++ tailWord_2547100).sum := by decide
  have hdescent : baseEnd_2547100 < baseStart_2547100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547145 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 5]
def baseStart_2547145 : Nat := 118140960795 + 2547145 * 2 ^ 59
def prefixEnd_2547145 : Nat := 4983230072969 + 3 ^ 40 * 2547145 * 2
def baseEnd_2547145 : Nat := 1307909681696542017173399

theorem tailTrace_2547145 : CollatzResearch.WordTrace tailWord_2547145 prefixEnd_2547145 1307909681696542017173399 := by
  unfold tailWord_2547145
  simp only [CollatzResearch.WordTrace]
  refine ⟨92902010357136157577578889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61934673571424105051719259 92902010357136157577578889)
  ·
    refine ⟨69676507767852118183184167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92902010357136157577578889 69676507767852118183184167)
    ·
      refine ⟨104514761651778177274776251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69676507767852118183184167 104514761651778177274776251)
      ·
        refine ⟨156772142477667265912164377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104514761651778177274776251 156772142477667265912164377)
        ·
          refine ⟨117579106858250449434123283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156772142477667265912164377 117579106858250449434123283)
          ·
            refine ⟨176368660287375674151184925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117579106858250449434123283 176368660287375674151184925)
            ·
              refine ⟨66138247607765877806694347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176368660287375674151184925 66138247607765877806694347)
              ·
                refine ⟨99207371411648816710041521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66138247607765877806694347 99207371411648816710041521)
                ·
                  refine ⟨74405528558736612532531141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99207371411648816710041521 74405528558736612532531141)
                  ·
                    refine ⟨13951036604763114849849589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 74405528558736612532531141 13951036604763114849849589)
                    ·
                      refine ⟨1307909681696542017173399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13951036604763114849849589 1307909681696542017173399)
                      ·
                        rfl

theorem cell23_2547145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 2, 4, 5].length) (baseStart_2547145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547145 prefixEnd_2547145 := by exact prefixLift 2547145
  have htrace : WordTrace (prefixWord ++ tailWord_2547145) baseStart_2547145 baseEnd_2547145 := by
    simpa [prefixWord, tailWord_2547145, baseEnd_2547145] using wordTrace_append hprefix tailTrace_2547145
  have hstable : (prefixWord ++ tailWord_2547145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547145).length < 2 ^ (prefixWord ++ tailWord_2547145).sum := by decide
  have hdescent : baseEnd_2547145 < baseStart_2547145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547152 : List Nat := [2, 1, 1, 1, 1, 2, 2, 7, 1, 5]
def baseStart_2547152 : Nat := 118140960795 + 2547152 * 2 ^ 59
def prefixEnd_2547152 : Nat := 4983230072969 + 3 ^ 40 * 2547152 * 2
def baseEnd_2547152 : Nat := 435971092020374496595289

theorem tailTrace_2547152 : CollatzResearch.WordTrace tailWord_2547152 prefixEnd_2547152 435971092020374496595289 := by
  unfold tailWord_2547152
  simp only [CollatzResearch.WordTrace]
  refine ⟨46451132834055398886541855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61934843778740531848722473 46451132834055398886541855)
  ·
    refine ⟨69676699251083098329812783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46451132834055398886541855 69676699251083098329812783)
    ·
      refine ⟨104515048876624647494719175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69676699251083098329812783 104515048876624647494719175)
      ·
        refine ⟨156772573314936971242078763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104515048876624647494719175 156772573314936971242078763)
        ·
          refine ⟨235158859972405456863118145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156772573314936971242078763 235158859972405456863118145)
          ·
            refine ⟨176369144979304092647338609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235158859972405456863118145 176369144979304092647338609)
            ·
              refine ⟨132276858734478069485503957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176369144979304092647338609 132276858734478069485503957)
              ·
                refine ⟨3100238876589329753566499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 132276858734478069485503957 3100238876589329753566499)
                ·
                  refine ⟨4650358314883994630349749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100238876589329753566499 4650358314883994630349749)
                  ·
                    refine ⟨435971092020374496595289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4650358314883994630349749 435971092020374496595289)
                    ·
                      rfl

theorem cell23_2547152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 7, 1, 5].length) (baseStart_2547152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547152 prefixEnd_2547152 := by exact prefixLift 2547152
  have htrace : WordTrace (prefixWord ++ tailWord_2547152) baseStart_2547152 baseEnd_2547152 := by
    simpa [prefixWord, tailWord_2547152, baseEnd_2547152] using wordTrace_append hprefix tailTrace_2547152
  have hstable : (prefixWord ++ tailWord_2547152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547152).length < 2 ^ (prefixWord ++ tailWord_2547152).sum := by decide
  have hdescent : baseEnd_2547152 < baseStart_2547152 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547156 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 6]
def baseStart_2547156 : Nat := 118140960795 + 2547156 * 2 ^ 59
def prefixEnd_2547156 : Nat := 4983230072969 + 3 ^ 40 * 2547156 * 2
def baseEnd_2547156 : Nat := 145323925553749052681761

theorem tailTrace_2547156 : CollatzResearch.WordTrace tailWord_2547156 prefixEnd_2547156 145323925553749052681761 := by
  unfold tailWord_2547156
  simp only [CollatzResearch.WordTrace]
  refine ⟨46451205780048153228114661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61934941040064204304152881 46451205780048153228114661)
  ·
    refine ⟨8709601083759028730271499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46451205780048153228114661 8709601083759028730271499)
    ·
      refine ⟨13064401625638543095407249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8709601083759028730271499 13064401625638543095407249)
      ·
        refine ⟨9798301219228907321555437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13064401625638543095407249 9798301219228907321555437)
        ·
          refine ⟨3674362957210840245583289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9798301219228907321555437 3674362957210840245583289)
          ·
            refine ⟨2755772217908130184187467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3674362957210840245583289 2755772217908130184187467)
            ·
              refine ⟨4133658326862195276281201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755772217908130184187467 4133658326862195276281201)
              ·
                refine ⟨3100243745146646457210901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4133658326862195276281201 3100243745146646457210901)
                ·
                  refine ⟨145323925553749052681761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3100243745146646457210901 145323925553749052681761)
                  ·
                    rfl

theorem cell23_2547156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 6].length) (baseStart_2547156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547156 prefixEnd_2547156 := by exact prefixLift 2547156
  have htrace : WordTrace (prefixWord ++ tailWord_2547156) baseStart_2547156 baseEnd_2547156 := by
    simpa [prefixWord, tailWord_2547156, baseEnd_2547156] using wordTrace_append hprefix tailTrace_2547156
  have hstable : (prefixWord ++ tailWord_2547156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547156).length < 2 ^ (prefixWord ++ tailWord_2547156).sum := by decide
  have hdescent : baseEnd_2547156 < baseStart_2547156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547159 : List Nat := [1, 1, 3, 2, 1, 1, 1, 6, 2, 3, 2]
def baseStart_2547159 : Nat := 118140960795 + 2547159 * 2 ^ 59
def prefixEnd_2547159 : Nat := 4983230072969 + 3 ^ 40 * 2547159 * 2
def baseEnd_2547159 : Nat := 1307916870425704962398335

theorem tailTrace_2547159 : CollatzResearch.WordTrace tailWord_2547159 prefixEnd_2547159 1307916870425704962398335 := by
  unfold tailWord_2547159
  simp only [CollatzResearch.WordTrace]
  refine ⟨92902520979085437968588531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61935013986056958645725687 92902520979085437968588531)
  ·
    refine ⟨139353781468628156952882797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92902520979085437968588531 139353781468628156952882797)
    ·
      refine ⟨52257668050735558857331049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139353781468628156952882797 52257668050735558857331049)
      ·
        refine ⟨39193251038051669142998287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52257668050735558857331049 39193251038051669142998287)
        ·
          refine ⟨58789876557077503714497431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39193251038051669142998287 58789876557077503714497431)
          ·
            refine ⟨88184814835616255571746147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58789876557077503714497431 88184814835616255571746147)
            ·
              refine ⟨132277222253424383357619221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88184814835616255571746147 132277222253424383357619221)
              ·
                refine ⟨6200494793129267969888401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 132277222253424383357619221 6200494793129267969888401)
                ·
                  refine ⟨4650371094846950977416301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6200494793129267969888401 4650371094846950977416301)
                  ·
                    refine ⟨1743889160567606616531113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4650371094846950977416301 1743889160567606616531113)
                    ·
                      refine ⟨1307916870425704962398335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1743889160567606616531113 1307916870425704962398335)
                      ·
                        rfl

theorem cell23_2547159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 6, 2, 3, 2].length) (baseStart_2547159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547159 prefixEnd_2547159 := by exact prefixLift 2547159
  have htrace : WordTrace (prefixWord ++ tailWord_2547159) baseStart_2547159 baseEnd_2547159 := by
    simpa [prefixWord, tailWord_2547159, baseEnd_2547159] using wordTrace_append hprefix tailTrace_2547159
  have hstable : (prefixWord ++ tailWord_2547159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547159).length < 2 ^ (prefixWord ++ tailWord_2547159).sum := by decide
  have hdescent : baseEnd_2547159 < baseStart_2547159 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547172 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 5, 1, 4]
def baseStart_2547172 : Nat := 118140960795 + 2547172 * 2 ^ 59
def prefixEnd_2547172 : Nat := 4983230072969 + 3 ^ 40 * 2547172 * 2
def baseEnd_2547172 : Nat := 1307923545674213411535775

theorem tailTrace_2547172 : CollatzResearch.WordTrace tailWord_2547172 prefixEnd_2547172 1307923545674213411535775 := by
  unfold tailWord_2547172
  simp only [CollatzResearch.WordTrace]
  refine ⟨46451497564019170594405885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61935330085358894125874513 46451497564019170594405885)
  ·
    refine ⟨17419311586507188972902207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 46451497564019170594405885 17419311586507188972902207)
    ·
      refine ⟨26128967379760783459353311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17419311586507188972902207 26128967379760783459353311)
      ·
        refine ⟨39193451069641175189029967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26128967379760783459353311 39193451069641175189029967)
        ·
          refine ⟨58790176604461762783544951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39193451069641175189029967 58790176604461762783544951)
          ·
            refine ⟨88185264906692644175317427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58790176604461762783544951 88185264906692644175317427)
            ·
              refine ⟨132277897360038966262976141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88185264906692644175317427 132277897360038966262976141)
              ·
                refine ⟨49604211510014612348616053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 132277897360038966262976141 49604211510014612348616053)
                ·
                  refine ⟨4650394829063869907682755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 49604211510014612348616053 4650394829063869907682755)
                  ·
                    refine ⟨6975592243595804861524133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4650394829063869907682755 6975592243595804861524133)
                    ·
                      refine ⟨1307923545674213411535775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6975592243595804861524133 1307923545674213411535775)
                      ·
                        rfl

theorem cell23_2547172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_2547172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547172 prefixEnd_2547172 := by exact prefixLift 2547172
  have htrace : WordTrace (prefixWord ++ tailWord_2547172) baseStart_2547172 baseEnd_2547172 := by
    simpa [prefixWord, tailWord_2547172, baseEnd_2547172] using wordTrace_append hprefix tailTrace_2547172
  have hstable : (prefixWord ++ tailWord_2547172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547172).length < 2 ^ (prefixWord ++ tailWord_2547172).sum := by decide
  have hdescent : baseEnd_2547172 < baseStart_2547172 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547186 : List Nat := [3, 2, 1, 4, 1, 2, 2, 2, 1, 5]
def baseStart_2547186 : Nat := 118140960795 + 2547186 * 2 ^ 59
def prefixEnd_2547186 : Nat := 4983230072969 + 3 ^ 40 * 2547186 * 2
def baseEnd_2547186 : Nat := 435976911467792118920237

theorem tailTrace_2547186 : CollatzResearch.WordTrace tailWord_2547186 prefixEnd_2547186 435976911467792118920237 := by
  unfold tailWord_2547186
  simp only [CollatzResearch.WordTrace]
  refine ⟨23225876437496905394955353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61935670499991747719880941 23225876437496905394955353)
  ·
    refine ⟨17419407328122679046216515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23225876437496905394955353 17419407328122679046216515)
    ·
      refine ⟨26129110992184018569324773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17419407328122679046216515 26129110992184018569324773)
      ·
        refine ⟨4899208311034503481748395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26129110992184018569324773 4899208311034503481748395)
        ·
          refine ⟨7348812466551755222622593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4899208311034503481748395 7348812466551755222622593)
          ·
            refine ⟨5511609349913816416966945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7348812466551755222622593 5511609349913816416966945)
            ·
              refine ⟨4133707012435362312725209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5511609349913816416966945 4133707012435362312725209)
              ·
                refine ⟨3100280259326521734543907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4133707012435362312725209 3100280259326521734543907)
                ·
                  refine ⟨4650420388989782601815861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100280259326521734543907 4650420388989782601815861)
                  ·
                    refine ⟨435976911467792118920237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4650420388989782601815861 435976911467792118920237)
                    ·
                      rfl

theorem cell23_2547186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_2547186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547186 prefixEnd_2547186 := by exact prefixLift 2547186
  have htrace : WordTrace (prefixWord ++ tailWord_2547186) baseStart_2547186 baseEnd_2547186 := by
    simpa [prefixWord, tailWord_2547186, baseEnd_2547186] using wordTrace_append hprefix tailTrace_2547186
  have hstable : (prefixWord ++ tailWord_2547186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547186).length < 2 ^ (prefixWord ++ tailWord_2547186).sum := by decide
  have hdescent : baseEnd_2547186 < baseStart_2547186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547195 : List Nat := [1, 1, 1, 1, 1, 3, 2, 13]
def baseStart_2547195 : Nat := 118140960795 + 2547195 * 2 ^ 59
def prefixEnd_2547195 : Nat := 4983230072969 + 3 ^ 40 * 2547195 * 2
def baseEnd_2547195 : Nat := 48442050212195067464747

theorem tailTrace_2547195 : CollatzResearch.WordTrace tailWord_2547195 prefixEnd_2547195 48442050212195067464747 := by
  unfold tailWord_2547195
  simp only [CollatzResearch.WordTrace]
  refine ⟨92903834006955016116899039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61935889337970010744599359 92903834006955016116899039)
  ·
    refine ⟨139355751010432524175348559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92903834006955016116899039 139355751010432524175348559)
    ·
      refine ⟨209033626515648786263022839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139355751010432524175348559 209033626515648786263022839)
      ·
        refine ⟨313550439773473179394534259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209033626515648786263022839 313550439773473179394534259)
        ·
          refine ⟨470325659660209769091801389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313550439773473179394534259 470325659660209769091801389)
          ·
            refine ⟨176372122372578663409425521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 470325659660209769091801389 176372122372578663409425521)
            ·
              refine ⟨132279091779433997557069141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176372122372578663409425521 132279091779433997557069141)
              ·
                refine ⟨48442050212195067464747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 132279091779433997557069141 48442050212195067464747)
                ·
                  rfl

theorem cell23_2547195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 13].length) (baseStart_2547195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547195 prefixEnd_2547195 := by exact prefixLift 2547195
  have htrace : WordTrace (prefixWord ++ tailWord_2547195) baseStart_2547195 baseEnd_2547195 := by
    simpa [prefixWord, tailWord_2547195, baseEnd_2547195] using wordTrace_append hprefix tailTrace_2547195
  have hstable : (prefixWord ++ tailWord_2547195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547195).length < 2 ^ (prefixWord ++ tailWord_2547195).sum := by decide
  have hdescent : baseEnd_2547195 < baseStart_2547195 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547209 : List Nat := [1, 2, 1, 1, 3, 1, 3, 5, 1, 2, 3]
def baseStart_2547209 : Nat := 118140960795 + 2547209 * 2 ^ 59
def prefixEnd_2547209 : Nat := 4983230072969 + 3 ^ 40 * 2547209 * 2
def baseEnd_2547209 : Nat := 1307942544458429766773105

theorem tailTrace_2547209 : CollatzResearch.WordTrace tailWord_2547209 prefixEnd_2547209 1307942544458429766773105 := by
  unfold tailWord_2547209
  simp only [CollatzResearch.WordTrace]
  refine ⟨92904344628904296507908681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61936229752602864338605787 92904344628904296507908681)
  ·
    refine ⟨69678258471678222380931511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92904344628904296507908681 69678258471678222380931511)
    ·
      refine ⟨104517387707517333571397267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69678258471678222380931511 104517387707517333571397267)
      ·
        refine ⟨156776081561276000357095901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104517387707517333571397267 156776081561276000357095901)
        ·
          refine ⟨58791030585478500133910963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156776081561276000357095901 58791030585478500133910963)
          ·
            refine ⟨88186545878217750200866445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58791030585478500133910963 88186545878217750200866445)
            ·
              refine ⟨33069954704331656325324917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 88186545878217750200866445 33069954704331656325324917)
              ·
                refine ⟨3100308253531092780499211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 33069954704331656325324917 3100308253531092780499211)
                ·
                  refine ⟨4650462380296639170748817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100308253531092780499211 4650462380296639170748817)
                  ·
                    refine ⟨3487846785222479378061613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4650462380296639170748817 3487846785222479378061613)
                    ·
                      refine ⟨1307942544458429766773105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3487846785222479378061613 1307942544458429766773105)
                      ·
                        rfl

theorem cell23_2547209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 5, 1, 2, 3].length) (baseStart_2547209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547209 prefixEnd_2547209 := by exact prefixLift 2547209
  have htrace : WordTrace (prefixWord ++ tailWord_2547209) baseStart_2547209 baseEnd_2547209 := by
    simpa [prefixWord, tailWord_2547209, baseEnd_2547209] using wordTrace_append hprefix tailTrace_2547209
  have hstable : (prefixWord ++ tailWord_2547209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547209).length < 2 ^ (prefixWord ++ tailWord_2547209).sum := by decide
  have hdescent : baseEnd_2547209 < baseStart_2547209 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547233 : List Nat := [1, 2, 3, 2, 2, 4, 2, 1, 2, 4]
def baseStart_2547233 : Nat := 118140960795 + 2547233 * 2 ^ 59
def prefixEnd_2547233 : Nat := 4983230072969 + 3 ^ 40 * 2547233 * 2
def baseEnd_2547233 : Nat := 435984955998045890957665

theorem tailTrace_2547233 : CollatzResearch.WordTrace tailWord_2547233 prefixEnd_2547233 435984955998045890957665 := by
  unfold tailWord_2547233
  simp only [CollatzResearch.WordTrace]
  refine ⟨92905219980817348606782353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61936813320544899071188235 92905219980817348606782353)
  ·
    refine ⟨69678914985613011455086765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92905219980817348606782353 69678914985613011455086765)
    ·
      refine ⟨26129593119604879295657537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69678914985613011455086765 26129593119604879295657537)
      ·
        refine ⟨19597194839703659471743153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26129593119604879295657537 19597194839703659471743153)
        ·
          refine ⟨14697896129777744603807365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19597194839703659471743153 14697896129777744603807365)
          ·
            refine ⟨2755855524333327113213881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14697896129777744603807365 2755855524333327113213881)
            ·
              refine ⟨2066891643249995334910411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755855524333327113213881 2066891643249995334910411)
              ·
                refine ⟨3100337464874993002365617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066891643249995334910411 3100337464874993002365617)
                ·
                  refine ⟨2325253098656244751774213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3100337464874993002365617 2325253098656244751774213)
                  ·
                    refine ⟨435984955998045890957665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2325253098656244751774213 435984955998045890957665)
                    ·
                      rfl

theorem cell23_2547233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 2, 1, 2, 4].length) (baseStart_2547233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547233 prefixEnd_2547233 := by exact prefixLift 2547233
  have htrace : WordTrace (prefixWord ++ tailWord_2547233) baseStart_2547233 baseEnd_2547233 := by
    simpa [prefixWord, tailWord_2547233, baseEnd_2547233] using wordTrace_append hprefix tailTrace_2547233
  have hstable : (prefixWord ++ tailWord_2547233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547233).length < 2 ^ (prefixWord ++ tailWord_2547233).sum := by decide
  have hdescent : baseEnd_2547233 < baseStart_2547233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547240 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 1, 1, 4]
def baseStart_2547240 : Nat := 118140960795 + 2547240 * 2 ^ 59
def prefixEnd_2547240 : Nat := 4983230072969 + 3 ^ 40 * 2547240 * 2
def baseEnd_2547240 : Nat := 1307958462358719145485463

theorem tailTrace_2547240 : CollatzResearch.WordTrace tailWord_2547240 prefixEnd_2547240 1307958462358719145485463 := by
  unfold tailWord_2547240
  simp only [CollatzResearch.WordTrace]
  refine ⟨46452737645895994401143587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61936983527861325868191449 46452737645895994401143587)
  ·
    refine ⟨69679106468843991601715381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46452737645895994401143587 69679106468843991601715381)
    ·
      refine ⟨6532416231454124212660817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 69679106468843991601715381 6532416231454124212660817)
      ·
        refine ⟨4899312173590593159495613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6532416231454124212660817 4899312173590593159495613)
        ·
          refine ⟨1837242065096472434810855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4899312173590593159495613 1837242065096472434810855)
          ·
            refine ⟨2755863097644708652216283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837242065096472434810855 2755863097644708652216283)
            ·
              refine ⟨4133794646467062978324425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2755863097644708652216283 4133794646467062978324425)
              ·
                refine ⟨3100345984850297233743319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4133794646467062978324425 3100345984850297233743319)
                ·
                  refine ⟨4650518977275445850614979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100345984850297233743319 4650518977275445850614979)
                  ·
                    refine ⟨6975778465913168775922469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4650518977275445850614979 6975778465913168775922469)
                    ·
                      refine ⟨1307958462358719145485463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6975778465913168775922469 1307958462358719145485463)
                      ·
                        rfl

theorem cell23_2547240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_2547240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547240 prefixEnd_2547240 := by exact prefixLift 2547240
  have htrace : WordTrace (prefixWord ++ tailWord_2547240) baseStart_2547240 baseEnd_2547240 := by
    simpa [prefixWord, tailWord_2547240, baseEnd_2547240] using wordTrace_append hprefix tailTrace_2547240
  have hstable : (prefixWord ++ tailWord_2547240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547240).length < 2 ^ (prefixWord ++ tailWord_2547240).sum := by decide
  have hdescent : baseEnd_2547240 < baseStart_2547240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547279 : List Nat := [1, 1, 2, 1, 1, 2, 3, 1, 5, 4, 2]
def baseStart_2547279 : Nat := 118140960795 + 2547279 * 2 ^ 59
def prefixEnd_2547279 : Nat := 4983230072969 + 3 ^ 40 * 2547279 * 2
def baseEnd_2547279 : Nat := 1307978488104244492897783

theorem tailTrace_2547279 : CollatzResearch.WordTrace tailWord_2547279 prefixEnd_2547279 1307978488104244492897783 := by
  unfold tailWord_2547279
  simp only [CollatzResearch.WordTrace]
  refine ⟨92906897738650698462956891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61937931825767132308637927 92906897738650698462956891)
  ·
    refine ⟨139360346607976047694435337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92906897738650698462956891 139360346607976047694435337)
    ·
      refine ⟨104520259955982035770826503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139360346607976047694435337 104520259955982035770826503)
      ·
        refine ⟨156780389933973053656239755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104520259955982035770826503 156780389933973053656239755)
        ·
          refine ⟨235170584900959580484359633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156780389933973053656239755 235170584900959580484359633)
          ·
            refine ⟨176377938675719685363269725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235170584900959580484359633 176377938675719685363269725)
            ·
              refine ⟨66141727003394882011226147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176377938675719685363269725 66141727003394882011226147)
              ·
                refine ⟨99212590505092323016839221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66141727003394882011226147 99212590505092323016839221)
                ·
                  refine ⟨9301180359852405282828677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99212590505092323016839221 9301180359852405282828677)
                  ·
                    refine ⟨1743971317472325990530377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9301180359852405282828677 1743971317472325990530377)
                    ·
                      refine ⟨1307978488104244492897783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1743971317472325990530377 1307978488104244492897783)
                      ·
                        rfl

theorem cell23_2547279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 1, 5, 4, 2].length) (baseStart_2547279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547279 prefixEnd_2547279 := by exact prefixLift 2547279
  have htrace : WordTrace (prefixWord ++ tailWord_2547279) baseStart_2547279 baseEnd_2547279 := by
    simpa [prefixWord, tailWord_2547279, baseEnd_2547279] using wordTrace_append hprefix tailTrace_2547279
  have hstable : (prefixWord ++ tailWord_2547279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547279).length < 2 ^ (prefixWord ++ tailWord_2547279).sum := by decide
  have hdescent : baseEnd_2547279 < baseStart_2547279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547296 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 6, 2, 2]
def baseStart_2547296 : Nat := 118140960795 + 2547296 * 2 ^ 59
def prefixEnd_2547296 : Nat := 4983230072969 + 3 ^ 40 * 2547296 * 2
def baseEnd_2547296 : Nat := 1307987217275370926385205

theorem tailTrace_2547296 : CollatzResearch.WordTrace tailWord_2547296 prefixEnd_2547296 1307987217275370926385205 := by
  unfold tailWord_2547296
  simp only [CollatzResearch.WordTrace]
  refine ⟨46453758889794555183162871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61938345186392740244217161 46453758889794555183162871)
  ·
    refine ⟨69680638334691832774744307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46453758889794555183162871 69680638334691832774744307)
    ·
      refine ⟨104520957502037749162116461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69680638334691832774744307 104520957502037749162116461)
      ·
        refine ⟨39195359063264155935793673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 104520957502037749162116461 39195359063264155935793673)
        ·
          refine ⟨29396519297448116951845255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 39195359063264155935793673 29396519297448116951845255)
          ·
            refine ⟨44094778946172175427767883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29396519297448116951845255 44094778946172175427767883)
            ·
              refine ⟨66142168419258263141651825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44094778946172175427767883 66142168419258263141651825)
              ·
                refine ⟨49606626314443697356238869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66142168419258263141651825 49606626314443697356238869)
                ·
                  refine ⟨2325310608489548313573697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 49606626314443697356238869 2325310608489548313573697)
                  ·
                    refine ⟨1743982956367161235180273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2325310608489548313573697 1743982956367161235180273)
                    ·
                      refine ⟨1307987217275370926385205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1743982956367161235180273 1307987217275370926385205)
                      ·
                        rfl

theorem cell23_2547296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 6, 2, 2].length) (baseStart_2547296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547296 prefixEnd_2547296 := by exact prefixLift 2547296
  have htrace : WordTrace (prefixWord ++ tailWord_2547296) baseStart_2547296 baseEnd_2547296 := by
    simpa [prefixWord, tailWord_2547296, baseEnd_2547296] using wordTrace_append hprefix tailTrace_2547296
  have hstable : (prefixWord ++ tailWord_2547296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547296).length < 2 ^ (prefixWord ++ tailWord_2547296).sum := by decide
  have hdescent : baseEnd_2547296 < baseStart_2547296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547317 : List Nat := [1, 3, 4, 2, 1, 3, 2, 1, 1, 3, 2]
def baseStart_2547317 : Nat := 118140960795 + 2547317 * 2 ^ 59
def prefixEnd_2547317 : Nat := 4983230072969 + 3 ^ 40 * 2547317 * 2
def baseEnd_2547317 : Nat := 1307998000369115344222609

theorem tailTrace_2547317 : CollatzResearch.WordTrace tailWord_2547317 prefixEnd_2547317 1307998000369115344222609 := by
  unfold tailWord_2547317
  simp only [CollatzResearch.WordTrace]
  refine ⟨92908283712513030952840205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61938855808342020635226803 92908283712513030952840205)
  ·
    refine ⟨34840606392192386607315077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92908283712513030952840205 34840606392192386607315077)
    ·
      refine ⟨6532613698536072488871577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34840606392192386607315077 6532613698536072488871577)
      ·
        refine ⟨4899460273902054366653683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6532613698536072488871577 4899460273902054366653683)
        ·
          refine ⟨7349190410853081549980525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4899460273902054366653683 7349190410853081549980525)
          ·
            refine ⟨2755946404069905581242697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7349190410853081549980525 2755946404069905581242697)
            ·
              refine ⟨2066959803052429185932023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2755946404069905581242697 2066959803052429185932023)
              ·
                refine ⟨3100439704578643778898035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2066959803052429185932023 3100439704578643778898035)
                ·
                  refine ⟨4650659556867965668347053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100439704578643778898035 4650659556867965668347053)
                  ·
                    refine ⟨1743997333825487125630145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4650659556867965668347053 1743997333825487125630145)
                    ·
                      refine ⟨1307998000369115344222609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1743997333825487125630145 1307998000369115344222609)
                      ·
                        rfl

theorem cell23_2547317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 3, 2, 1, 1, 3, 2].length) (baseStart_2547317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547317 prefixEnd_2547317 := by exact prefixLift 2547317
  have htrace : WordTrace (prefixWord ++ tailWord_2547317) baseStart_2547317 baseEnd_2547317 := by
    simpa [prefixWord, tailWord_2547317, baseEnd_2547317] using wordTrace_append hprefix tailTrace_2547317
  have hstable : (prefixWord ++ tailWord_2547317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547317).length < 2 ^ (prefixWord ++ tailWord_2547317).sum := by decide
  have hdescent : baseEnd_2547317 < baseStart_2547317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547386 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4]
def baseStart_2547386 : Nat := 118140960795 + 2547386 * 2 ^ 59
def prefixEnd_2547386 : Nat := 4983230072969 + 3 ^ 40 * 2547386 * 2
def baseEnd_2547386 : Nat := 1308033430534275574259791

theorem tailTrace_2547386 : CollatzResearch.WordTrace tailWord_2547386 prefixEnd_2547386 1308033430534275574259791 := by
  unfold tailWord_2547386
  simp only [CollatzResearch.WordTrace]
  refine ⟨23227700087315763934275503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61940533566175370491401341 23227700087315763934275503)
  ·
    refine ⟨34841550130973645901413255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23227700087315763934275503 34841550130973645901413255)
    ·
      refine ⟨52262325196460468852119883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34841550130973645901413255 52262325196460468852119883)
      ·
        refine ⟨78393487794690703278179825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52262325196460468852119883 78393487794690703278179825)
        ·
          refine ⟨58795115846018027458634869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78393487794690703278179825 58795115846018027458634869)
          ·
            refine ⟨5512042110564190074247019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 58795115846018027458634869 5512042110564190074247019)
            ·
              refine ⟨8268063165846285111370529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5512042110564190074247019 8268063165846285111370529)
              ·
                refine ⟨6201047374384713833527897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8268063165846285111370529 6201047374384713833527897)
                ·
                  refine ⟨4650785530788535375145923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6201047374384713833527897 4650785530788535375145923)
                  ·
                    refine ⟨6976178296182803062718885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4650785530788535375145923 6976178296182803062718885)
                    ·
                      refine ⟨1308033430534275574259791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6976178296182803062718885 1308033430534275574259791)
                      ·
                        rfl

theorem cell23_2547386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_2547386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547386 prefixEnd_2547386 := by exact prefixLift 2547386
  have htrace : WordTrace (prefixWord ++ tailWord_2547386) baseStart_2547386 baseEnd_2547386 := by
    simpa [prefixWord, tailWord_2547386, baseEnd_2547386] using wordTrace_append hprefix tailTrace_2547386
  have hstable : (prefixWord ++ tailWord_2547386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547386).length < 2 ^ (prefixWord ++ tailWord_2547386).sum := by decide
  have hdescent : baseEnd_2547386 < baseStart_2547386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547406 : List Nat := [4, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_2547406 : Nat := 118140960795 + 2547406 * 2 ^ 59
def prefixEnd_2547406 : Nat := 4983230072969 + 3 ^ 40 * 2547406 * 2
def baseEnd_2547406 : Nat := 1308043700147365496009699

theorem tailTrace_2547406 : CollatzResearch.WordTrace tailWord_2547406 prefixEnd_2547406 1308043700147365496009699 := by
  unfold tailWord_2547406
  simp only [CollatzResearch.WordTrace]
  refine ⟨11613941226148824894103759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 61941019872793732768553381 11613941226148824894103759)
  ·
    refine ⟨17420911839223237341155639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11613941226148824894103759 17420911839223237341155639)
    ·
      refine ⟨26131367758834856011733459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17420911839223237341155639 26131367758834856011733459)
      ·
        refine ⟨39197051638252284017600189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26131367758834856011733459 39197051638252284017600189)
        ·
          refine ⟨14698894364344606506600071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39197051638252284017600189 14698894364344606506600071)
          ·
            refine ⟨22048341546516909759900107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14698894364344606506600071 22048341546516909759900107)
            ·
              refine ⟨33072512319775364639850161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22048341546516909759900107 33072512319775364639850161)
              ·
                refine ⟨24804384239831523479887621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 33072512319775364639850161 24804384239831523479887621)
                ·
                  refine ⟨4650822044968410652478929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24804384239831523479887621 4650822044968410652478929)
                  ·
                    refine ⟨3488116533726307989359197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4650822044968410652478929 3488116533726307989359197)
                    ·
                      refine ⟨1308043700147365496009699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3488116533726307989359197 1308043700147365496009699)
                      ·
                        rfl

theorem cell23_2547406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_2547406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547406 prefixEnd_2547406 := by exact prefixLift 2547406
  have htrace : WordTrace (prefixWord ++ tailWord_2547406) baseStart_2547406 baseEnd_2547406 := by
    simpa [prefixWord, tailWord_2547406, baseEnd_2547406] using wordTrace_append hprefix tailTrace_2547406
  have hstable : (prefixWord ++ tailWord_2547406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547406).length < 2 ^ (prefixWord ++ tailWord_2547406).sum := by decide
  have hdescent : baseEnd_2547406 < baseStart_2547406 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547420 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 2, 1, 4]
def baseStart_2547420 : Nat := 118140960795 + 2547420 * 2 ^ 59
def prefixEnd_2547420 : Nat := 4983230072969 + 3 ^ 40 * 2547420 * 2
def baseEnd_2547420 : Nat := 1308050888876528441234635

theorem tailTrace_2547420 : CollatzResearch.WordTrace tailWord_2547420 prefixEnd_2547420 1308050888876528441234635 := by
  unfold tailWord_2547420
  simp only [CollatzResearch.WordTrace]
  refine ⟨46456020215569939771919857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61941360287426586362559809 46456020215569939771919857)
  ·
    refine ⟨34842015161677454828939893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46456020215569939771919857 34842015161677454828939893)
    ·
      refine ⟨3266438921407261390213115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34842015161677454828939893 3266438921407261390213115)
      ·
        refine ⟨4899658382110892085319673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3266438921407261390213115 4899658382110892085319673)
        ·
          refine ⟨3674743786583169063989755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4899658382110892085319673 3674743786583169063989755)
          ·
            refine ⟨5512115679874753595984633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3674743786583169063989755 5512115679874753595984633)
            ·
              refine ⟨4134086759906065196988475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5512115679874753595984633 4134086759906065196988475)
              ·
                refine ⟨6201130139859097795482713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4134086759906065196988475 6201130139859097795482713)
                ·
                  refine ⟨4650847604894323346612035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6201130139859097795482713 4650847604894323346612035)
                  ·
                    refine ⟨6976271407341485019918053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4650847604894323346612035 6976271407341485019918053)
                    ·
                      refine ⟨1308050888876528441234635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6976271407341485019918053 1308050888876528441234635)
                      ·
                        rfl

theorem cell23_2547420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 1, 4].length) (baseStart_2547420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547420 prefixEnd_2547420 := by exact prefixLift 2547420
  have htrace : WordTrace (prefixWord ++ tailWord_2547420) baseStart_2547420 baseEnd_2547420 := by
    simpa [prefixWord, tailWord_2547420, baseEnd_2547420] using wordTrace_append hprefix tailTrace_2547420
  have hstable : (prefixWord ++ tailWord_2547420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547420).length < 2 ^ (prefixWord ++ tailWord_2547420).sum := by decide
  have hdescent : baseEnd_2547420 < baseStart_2547420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547493 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 4]
def baseStart_2547493 : Nat := 118140960795 + 2547493 * 2 ^ 59
def prefixEnd_2547493 : Nat := 4983230072969 + 3 ^ 40 * 2547493 * 2
def baseEnd_2547493 : Nat := 1308088372964306655621799

theorem tailTrace_2547493 : CollatzResearch.WordTrace tailWord_2547493 prefixEnd_2547493 1308088372964306655621799 := by
  unfold tailWord_2547493
  simp only [CollatzResearch.WordTrace]
  refine ⟨92914702959875413011247133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61943135306583608674164755 92914702959875413011247133)
  ·
    refine ⟨34843013609953279879217675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92914702959875413011247133 34843013609953279879217675)
    ·
      refine ⟨52264520414929919818826513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34843013609953279879217675 52264520414929919818826513)
      ·
        refine ⟨39198390311197439864119885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52264520414929919818826513 39198390311197439864119885)
        ·
          refine ⟨14699396366699039949044957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 39198390311197439864119885 14699396366699039949044957)
          ·
            refine ⟨5512273637512139980891859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14699396366699039949044957 5512273637512139980891859)
            ·
              refine ⟨8268410456268209971337789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5512273637512139980891859 8268410456268209971337789)
              ·
                refine ⟨3100653921100578739251671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8268410456268209971337789 3100653921100578739251671)
                ·
                  refine ⟨4650980881650868108877507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100653921100578739251671 4650980881650868108877507)
                  ·
                    refine ⟨6976471322476302163316261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4650980881650868108877507 6976471322476302163316261)
                    ·
                      refine ⟨1308088372964306655621799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6976471322476302163316261 1308088372964306655621799)
                      ·
                        rfl

theorem cell23_2547493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_2547493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547493 prefixEnd_2547493 := by exact prefixLift 2547493
  have htrace : WordTrace (prefixWord ++ tailWord_2547493) baseStart_2547493 baseEnd_2547493 := by
    simpa [prefixWord, tailWord_2547493, baseEnd_2547493] using wordTrace_append hprefix tailTrace_2547493
  have hstable : (prefixWord ++ tailWord_2547493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547493).length < 2 ^ (prefixWord ++ tailWord_2547493).sum := by decide
  have hdescent : baseEnd_2547493 < baseStart_2547493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547523 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 4]
def baseStart_2547523 : Nat := 118140960795 + 2547523 * 2 ^ 59
def prefixEnd_2547523 : Nat := 4983230072969 + 3 ^ 40 * 2547523 * 2
def baseEnd_2547523 : Nat := 1308103777383941538246661

theorem tailTrace_2547523 : CollatzResearch.WordTrace tailWord_2547523 prefixEnd_2547523 1308103777383941538246661 := by
  unfold tailWord_2547523
  simp only [CollatzResearch.WordTrace]
  refine ⟨92915797149766728134839223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61943864766511152089892815 92915797149766728134839223)
  ·
    refine ⟨139373695724650092202258835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92915797149766728134839223 139373695724650092202258835)
    ·
      refine ⟨209060543586975138303388253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139373695724650092202258835 209060543586975138303388253)
      ·
        refine ⟨78397703845115676863770595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209060543586975138303388253 78397703845115676863770595)
        ·
          refine ⟨117596555767673515295655893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78397703845115676863770595 117596555767673515295655893)
          ·
            refine ⟨2756169275804848014741935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 117596555767673515295655893 2756169275804848014741935)
            ·
              refine ⟨4134253913707272022112903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756169275804848014741935 4134253913707272022112903)
              ·
                refine ⟨6201380870560908033169355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4134253913707272022112903 6201380870560908033169355)
                ·
                  refine ⟨9302071305841362049754033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6201380870560908033169355 9302071305841362049754033)
                  ·
                    refine ⟨6976553479381021537315525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9302071305841362049754033 6976553479381021537315525)
                    ·
                      refine ⟨1308103777383941538246661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6976553479381021537315525 1308103777383941538246661)
                      ·
                        rfl

theorem cell23_2547523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 2, 4].length) (baseStart_2547523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547523 prefixEnd_2547523 := by exact prefixLift 2547523
  have htrace : WordTrace (prefixWord ++ tailWord_2547523) baseStart_2547523 baseEnd_2547523 := by
    simpa [prefixWord, tailWord_2547523, baseEnd_2547523] using wordTrace_append hprefix tailTrace_2547523
  have hstable : (prefixWord ++ tailWord_2547523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547523).length < 2 ^ (prefixWord ++ tailWord_2547523).sum := by decide
  have hdescent : baseEnd_2547523 < baseStart_2547523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547533 : List Nat := [1, 6, 1, 2, 1, 2, 1, 9]
def baseStart_2547533 : Nat := 118140960795 + 2547533 * 2 ^ 59
def prefixEnd_2547533 : Nat := 4983230072969 + 3 ^ 40 * 2547533 * 2
def baseEnd_2547533 : Nat := 48448478229277277745245

theorem tailTrace_2547533 : CollatzResearch.WordTrace tailWord_2547533 prefixEnd_2547533 48448478229277277745245 := by
  unfold tailWord_2547533
  simp only [CollatzResearch.WordTrace]
  refine ⟨92916161879730499842703253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61944107919820333228468835 92916161879730499842703253)
  ·
    refine ⟨4355445088112367180126715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 92916161879730499842703253 4355445088112367180126715)
    ·
      refine ⟨6533167632168550770190073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4355445088112367180126715 6533167632168550770190073)
      ·
        refine ⟨4899875724126413077642555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6533167632168550770190073 4899875724126413077642555)
        ·
          refine ⟨7349813586189619616463833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4899875724126413077642555 7349813586189619616463833)
          ·
            refine ⟨5512360189642214712347875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7349813586189619616463833 5512360189642214712347875)
            ·
              refine ⟨8268540284463322068521813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5512360189642214712347875 8268540284463322068521813)
              ·
                refine ⟨48448478229277277745245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 8268540284463322068521813 48448478229277277745245)
                ·
                  rfl

theorem cell23_2547533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 1, 9].length) (baseStart_2547533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547533 prefixEnd_2547533 := by exact prefixLift 2547533
  have htrace : WordTrace (prefixWord ++ tailWord_2547533) baseStart_2547533 baseEnd_2547533 := by
    simpa [prefixWord, tailWord_2547533, baseEnd_2547533] using wordTrace_append hprefix tailTrace_2547533
  have hstable : (prefixWord ++ tailWord_2547533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547533).length < 2 ^ (prefixWord ++ tailWord_2547533).sum := by decide
  have hdescent : baseEnd_2547533 < baseStart_2547533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547560 : List Nat := [2, 1, 4, 2, 1, 1, 2, 4, 2, 1, 3]
def baseStart_2547560 : Nat := 118140960795 + 2547560 * 2 ^ 59
def prefixEnd_2547560 : Nat := 4983230072969 + 3 ^ 40 * 2547560 * 2
def baseEnd_2547560 : Nat := 1308122776168157893483991

theorem tailTrace_2547560 : CollatzResearch.WordTrace tailWord_2547560 prefixEnd_2547560 1308122776168157893483991 := by
  unfold tailWord_2547560
  simp only [CollatzResearch.WordTrace]
  refine ⟨46458573325316341726968067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61944764433755122302624089 46458573325316341726968067)
  ·
    refine ⟨69687859987974512590452101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46458573325316341726968067 69687859987974512590452101)
    ·
      refine ⟨13066473747745221110709769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69687859987974512590452101 13066473747745221110709769)
      ·
        refine ⟨9799855310808915833032327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13066473747745221110709769 9799855310808915833032327)
        ·
          refine ⟨14699782966213373749548491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9799855310808915833032327 14699782966213373749548491)
          ·
            refine ⟨22049674449320060624322737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14699782966213373749548491 22049674449320060624322737)
            ·
              refine ⟨16537255836990045468242053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22049674449320060624322737 16537255836990045468242053)
              ·
                refine ⟨3100735469435633525295385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16537255836990045468242053 3100735469435633525295385)
                ·
                  refine ⟨2325551602076725143971539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3100735469435633525295385 2325551602076725143971539)
                  ·
                    refine ⟨3488327403115087715957309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2325551602076725143971539 3488327403115087715957309)
                    ·
                      refine ⟨1308122776168157893483991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3488327403115087715957309 1308122776168157893483991)
                      ·
                        rfl

theorem cell23_2547560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_2547560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547560 prefixEnd_2547560 := by exact prefixLift 2547560
  have htrace : WordTrace (prefixWord ++ tailWord_2547560) baseStart_2547560 baseEnd_2547560 := by
    simpa [prefixWord, tailWord_2547560, baseEnd_2547560] using wordTrace_append hprefix tailTrace_2547560
  have hstable : (prefixWord ++ tailWord_2547560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547560).length < 2 ^ (prefixWord ++ tailWord_2547560).sum := by decide
  have hdescent : baseEnd_2547560 < baseStart_2547560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547583 : List Nat := [1, 1, 2, 2, 1, 1, 3, 5, 1, 4, 2]
def baseStart_2547583 : Nat := 118140960795 + 2547583 * 2 ^ 59
def prefixEnd_2547583 : Nat := 4983230072969 + 3 ^ 40 * 2547583 * 2
def baseEnd_2547583 : Nat := 1308134586223211303496385

theorem tailTrace_2547583 : CollatzResearch.WordTrace tailWord_2547583 prefixEnd_2547583 1308134586223211303496385 := by
  unfold tailWord_2547583
  simp only [CollatzResearch.WordTrace]
  refine ⟨92917985529549358382023403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61945323686366238921348935 92917985529549358382023403)
  ·
    refine ⟨139376978294324037573035105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92917985529549358382023403 139376978294324037573035105)
    ·
      refine ⟨104532733720743028179776329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139376978294324037573035105 104532733720743028179776329)
      ·
        refine ⟨78399550290557271134832247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104532733720743028179776329 78399550290557271134832247)
        ·
          refine ⟨117599325435835906702248371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78399550290557271134832247 117599325435835906702248371)
          ·
            refine ⟨176398988153753860053372557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117599325435835906702248371 176398988153753860053372557)
            ·
              refine ⟨66149620557657697520014709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 176398988153753860053372557 66149620557657697520014709)
              ·
                refine ⟨6201526927280409142501379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 66149620557657697520014709 6201526927280409142501379)
                ·
                  refine ⟨9302290390920613713752069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6201526927280409142501379 9302290390920613713752069)
                  ·
                    refine ⟨1744179448297615071328513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9302290390920613713752069 1744179448297615071328513)
                    ·
                      refine ⟨1308134586223211303496385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744179448297615071328513 1308134586223211303496385)
                      ·
                        rfl

theorem cell23_2547583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 1, 4, 2].length) (baseStart_2547583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547583 prefixEnd_2547583 := by exact prefixLift 2547583
  have htrace : WordTrace (prefixWord ++ tailWord_2547583) baseStart_2547583 baseEnd_2547583 := by
    simpa [prefixWord, tailWord_2547583, baseEnd_2547583] using wordTrace_append hprefix tailTrace_2547583
  have hstable : (prefixWord ++ tailWord_2547583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547583).length < 2 ^ (prefixWord ++ tailWord_2547583).sum := by decide
  have hdescent : baseEnd_2547583 < baseStart_2547583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547587 : List Nat := [1, 1, 1, 3, 4, 4, 1, 2, 1, 3, 2]
def baseStart_2547587 : Nat := 118140960795 + 2547587 * 2 ^ 59
def prefixEnd_2547587 : Nat := 4983230072969 + 3 ^ 40 * 2547587 * 2
def baseEnd_2547587 : Nat := 1308136640145829287846367

theorem tailTrace_2547587 : CollatzResearch.WordTrace tailWord_2547587 prefixEnd_2547587 1308136640145829287846367 := by
  unfold tailWord_2547587
  simp only [CollatzResearch.WordTrace]
  refine ⟨92918131421534867065169015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61945420947689911376779343 92918131421534867065169015)
  ·
    refine ⟨139377197132302300597753523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92918131421534867065169015 139377197132302300597753523)
    ·
      refine ⟨209065795698453450896630285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139377197132302300597753523 209065795698453450896630285)
      ·
        refine ⟨78399673386920044086236357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 209065795698453450896630285 78399673386920044086236357)
        ·
          refine ⟨14699938760047508266169317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 78399673386920044086236357 14699938760047508266169317)
          ·
            refine ⟨2756238517508907799906747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14699938760047508266169317 2756238517508907799906747)
            ·
              refine ⟨4134357776263361699860121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756238517508907799906747 4134357776263361699860121)
              ·
                refine ⟨3100768332197521274895091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4134357776263361699860121 3100768332197521274895091)
                ·
                  refine ⟨4651152498296281912342637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100768332197521274895091 4651152498296281912342637)
                  ·
                    refine ⟨1744182186861105717128489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4651152498296281912342637 1744182186861105717128489)
                    ·
                      refine ⟨1308136640145829287846367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744182186861105717128489 1308136640145829287846367)
                      ·
                        rfl

theorem cell23_2547587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 4, 1, 2, 1, 3, 2].length) (baseStart_2547587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547587 prefixEnd_2547587 := by exact prefixLift 2547587
  have htrace : WordTrace (prefixWord ++ tailWord_2547587) baseStart_2547587 baseEnd_2547587 := by
    simpa [prefixWord, tailWord_2547587, baseEnd_2547587] using wordTrace_append hprefix tailTrace_2547587
  have hstable : (prefixWord ++ tailWord_2547587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547587).length < 2 ^ (prefixWord ++ tailWord_2547587).sum := by decide
  have hdescent : baseEnd_2547587 < baseStart_2547587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547596 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 4, 2, 4]
def baseStart_2547596 : Nat := 118140960795 + 2547596 * 2 ^ 59
def prefixEnd_2547596 : Nat := 4983230072969 + 3 ^ 40 * 2547596 * 2
def baseEnd_2547596 : Nat := 1308141261471719752633825

theorem tailTrace_2547596 : CollatzResearch.WordTrace tailWord_2547596 prefixEnd_2547596 1308141261471719752633825 := by
  unfold tailWord_2547596
  simp only [CollatzResearch.WordTrace]
  refine ⟨46459229839251130801123321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61945639785668174401497761 46459229839251130801123321)
  ·
    refine ⟨34844422379438348100842491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46459229839251130801123321 34844422379438348100842491)
    ·
      refine ⟨52266633569157522151263737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34844422379438348100842491 52266633569157522151263737)
      ·
        refine ⟨39199975176868141613447803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52266633569157522151263737 39199975176868141613447803)
        ·
          refine ⟨58799962765302212420171705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39199975176868141613447803 58799962765302212420171705)
          ·
            refine ⟨44099972073976659315128779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58799962765302212420171705 44099972073976659315128779)
            ·
              refine ⟨66149958110964988972693169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44099972073976659315128779 66149958110964988972693169)
              ·
                refine ⟨49612468583223741729519877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66149958110964988972693169 49612468583223741729519877)
                ·
                  refine ⟨9302337859354451574284977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 49612468583223741729519877 9302337859354451574284977)
                  ·
                    refine ⟨6976753394515838680713733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9302337859354451574284977 6976753394515838680713733)
                    ·
                      refine ⟨1308141261471719752633825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6976753394515838680713733 1308141261471719752633825)
                      ·
                        rfl

theorem cell23_2547596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 2, 4].length) (baseStart_2547596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547596 prefixEnd_2547596 := by exact prefixLift 2547596
  have htrace : WordTrace (prefixWord ++ tailWord_2547596) baseStart_2547596 baseEnd_2547596 := by
    simpa [prefixWord, tailWord_2547596, baseEnd_2547596] using wordTrace_append hprefix tailTrace_2547596
  have hstable : (prefixWord ++ tailWord_2547596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547596).length < 2 ^ (prefixWord ++ tailWord_2547596).sum := by decide
  have hdescent : baseEnd_2547596 < baseStart_2547596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547604 : List Nat := [2, 4, 2, 1, 1, 3, 3, 1, 1, 3, 2]
def baseStart_2547604 : Nat := 118140960795 + 2547604 * 2 ^ 59
def prefixEnd_2547604 : Nat := 4983230072969 + 3 ^ 40 * 2547604 * 2
def baseEnd_2547604 : Nat := 1308145369316955721333789

theorem tailTrace_2547604 : CollatzResearch.WordTrace tailWord_2547604 prefixEnd_2547604 1308145369316955721333789 := by
  unfold tailWord_2547604
  simp only [CollatzResearch.WordTrace]
  refine ⟨46459375731236639484268933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61945834308315519312358577 46459375731236639484268933)
  ·
    refine ⟨8711132949606869903300425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 46459375731236639484268933 8711132949606869903300425)
    ·
      refine ⟨6533349712205152427475319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8711132949606869903300425 6533349712205152427475319)
      ·
        refine ⟨9800024568307728641212979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6533349712205152427475319 9800024568307728641212979)
        ·
          refine ⟨14700036852461592961819469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9800024568307728641212979 14700036852461592961819469)
          ·
            refine ⟨5512513819673097360682301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14700036852461592961819469 5512513819673097360682301)
            ·
              refine ⟨2067192682377411510255863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5512513819673097360682301 2067192682377411510255863)
              ·
                refine ⟨3100789023566117265383795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067192682377411510255863 3100789023566117265383795)
                ·
                  refine ⟨4651183535349175898075693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100789023566117265383795 4651183535349175898075693)
                  ·
                    refine ⟨1744193825755940961778385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4651183535349175898075693 1744193825755940961778385)
                    ·
                      refine ⟨1308145369316955721333789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744193825755940961778385 1308145369316955721333789)
                      ·
                        rfl

theorem cell23_2547604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 3, 1, 1, 3, 2].length) (baseStart_2547604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547604 prefixEnd_2547604 := by exact prefixLift 2547604
  have htrace : WordTrace (prefixWord ++ tailWord_2547604) baseStart_2547604 baseEnd_2547604 := by
    simpa [prefixWord, tailWord_2547604, baseEnd_2547604] using wordTrace_append hprefix tailTrace_2547604
  have hstable : (prefixWord ++ tailWord_2547604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547604).length < 2 ^ (prefixWord ++ tailWord_2547604).sum := by decide
  have hdescent : baseEnd_2547604 < baseStart_2547604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547633 : List Nat := [1, 2, 2, 4, 2, 1, 1, 1, 1, 5, 3]
def baseStart_2547633 : Nat := 118140960795 + 2547633 * 2 ^ 59
def prefixEnd_2547633 : Nat := 4983230072969 + 3 ^ 40 * 2547633 * 2
def baseEnd_2547633 : Nat := 1308160260255936107871155

theorem tailTrace_2547633 : CollatzResearch.WordTrace tailWord_2547633 prefixEnd_2547633 1308160260255936107871155 := by
  unfold tailWord_2547633
  simp only [CollatzResearch.WordTrace]
  refine ⟨92919809179368216921343553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61946539452912144614229035 92919809179368216921343553)
  ·
    refine ⟨69689856884526162691007665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92919809179368216921343553 69689856884526162691007665)
    ·
      refine ⟨52267392663394622018255749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69689856884526162691007665 52267392663394622018255749)
      ·
        refine ⟨9800136124386491628422953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52267392663394622018255749 9800136124386491628422953)
        ·
          refine ⟨7350102093289868721317215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9800136124386491628422953 7350102093289868721317215)
          ·
            refine ⟨11025153139934803081975823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7350102093289868721317215 11025153139934803081975823)
            ·
              refine ⟨16537729709902204622963735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11025153139934803081975823 16537729709902204622963735)
              ·
                refine ⟨24806594564853306934445603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16537729709902204622963735 24806594564853306934445603)
                ·
                  refine ⟨37209891847279960401668405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24806594564853306934445603 37209891847279960401668405)
                  ·
                    refine ⟨3488427360682496287656413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 37209891847279960401668405 3488427360682496287656413)
                    ·
                      refine ⟨1308160260255936107871155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3488427360682496287656413 1308160260255936107871155)
                      ·
                        rfl

theorem cell23_2547633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_2547633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547633 prefixEnd_2547633 := by exact prefixLift 2547633
  have htrace : WordTrace (prefixWord ++ tailWord_2547633) baseStart_2547633 baseEnd_2547633 := by
    simpa [prefixWord, tailWord_2547633, baseEnd_2547633] using wordTrace_append hprefix tailTrace_2547633
  have hstable : (prefixWord ++ tailWord_2547633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547633).length < 2 ^ (prefixWord ++ tailWord_2547633).sum := by decide
  have hdescent : baseEnd_2547633 < baseStart_2547633 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547690 : List Nat := [3, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2]
def baseStart_2547690 : Nat := 118140960795 + 2547690 * 2 ^ 59
def prefixEnd_2547690 : Nat := 4983230072969 + 3 ^ 40 * 2547690 * 2
def baseEnd_2547690 : Nat := 1308189528653242384858393

theorem tailTrace_2547690 : CollatzResearch.WordTrace tailWord_2547690 prefixEnd_2547690 1308189528653242384858393 := by
  unfold tailWord_2547690
  simp only [CollatzResearch.WordTrace]
  refine ⟨23230472035040428914042131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61947925426774477104112349 23230472035040428914042131)
  ·
    refine ⟨34845708052560643371063197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23230472035040428914042131 34845708052560643371063197)
    ·
      refine ⟨13067140519710241264148699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34845708052560643371063197 13067140519710241264148699)
      ·
        refine ⟨19600710779565361896223049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13067140519710241264148699 19600710779565361896223049)
        ·
          refine ⟨14700533084674021422167287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19600710779565361896223049 14700533084674021422167287)
          ·
            refine ⟨22050799627011032133250931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14700533084674021422167287 22050799627011032133250931)
            ·
              refine ⟨33076199440516548199876397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22050799627011032133250931 33076199440516548199876397)
              ·
                refine ⟨12403574790193705574953649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 33076199440516548199876397 12403574790193705574953649)
                ·
                  refine ⟨9302681092645279181215237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12403574790193705574953649 9302681092645279181215237)
                  ·
                    refine ⟨1744252704870989846477857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9302681092645279181215237 1744252704870989846477857)
                    ·
                      refine ⟨1308189528653242384858393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744252704870989846477857 1308189528653242384858393)
                      ·
                        rfl

theorem cell23_2547690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 1, 3, 2, 4, 2].length) (baseStart_2547690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547690 prefixEnd_2547690 := by exact prefixLift 2547690
  have htrace : WordTrace (prefixWord ++ tailWord_2547690) baseStart_2547690 baseEnd_2547690 := by
    simpa [prefixWord, tailWord_2547690, baseEnd_2547690] using wordTrace_append hprefix tailTrace_2547690
  have hstable : (prefixWord ++ tailWord_2547690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547690).length < 2 ^ (prefixWord ++ tailWord_2547690).sum := by decide
  have hdescent : baseEnd_2547690 < baseStart_2547690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547706 : List Nat := [3, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9]
def baseStart_2547706 : Nat := 118140960795 + 2547706 * 2 ^ 59
def prefixEnd_2547706 : Nat := 4983230072969 + 3 ^ 40 * 2547706 * 2
def baseEnd_2547706 : Nat := 1308197744343714322258319

theorem tailTrace_2547706 : CollatzResearch.WordTrace tailWord_2547706 prefixEnd_2547706 1308197744343714322258319 := by
  unfold tailWord_2547706
  simp only [CollatzResearch.WordTrace]
  refine ⟨23230617927025937597187743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61948314472069166925833981 23230617927025937597187743)
  ·
    refine ⟨34845926890538906395781615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23230617927025937597187743 34845926890538906395781615)
    ·
      refine ⟨52268890335808359593672423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34845926890538906395781615 52268890335808359593672423)
      ·
        refine ⟨78403335503712539390508635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52268890335808359593672423 78403335503712539390508635)
        ·
          refine ⟨117605003255568809085762953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78403335503712539390508635 117605003255568809085762953)
          ·
            refine ⟨88203752441676606814322215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 117605003255568809085762953 88203752441676606814322215)
            ·
              refine ⟨132305628662514910221483323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 88203752441676606814322215 132305628662514910221483323)
              ·
                refine ⟨198458442993772365332224985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132305628662514910221483323 198458442993772365332224985)
                ·
                  refine ⟨148843832245329273999168739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 198458442993772365332224985 148843832245329273999168739)
                  ·
                    refine ⟨223265748367993910998753109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 148843832245329273999168739 223265748367993910998753109)
                    ·
                      refine ⟨1308197744343714322258319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 223265748367993910998753109 1308197744343714322258319)
                      ·
                        rfl

theorem cell23_2547706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_2547706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547706 prefixEnd_2547706 := by exact prefixLift 2547706
  have htrace : WordTrace (prefixWord ++ tailWord_2547706) baseStart_2547706 baseEnd_2547706 := by
    simpa [prefixWord, tailWord_2547706, baseEnd_2547706] using wordTrace_append hprefix tailTrace_2547706
  have hstable : (prefixWord ++ tailWord_2547706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547706).length < 2 ^ (prefixWord ++ tailWord_2547706).sum := by decide
  have hdescent : baseEnd_2547706 < baseStart_2547706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547717 : List Nat := [1, 3, 1, 1, 2, 4, 3, 3, 1, 4]
def baseStart_2547717 : Nat := 118140960795 + 2547717 * 2 ^ 59
def prefixEnd_2547717 : Nat := 4983230072969 + 3 ^ 40 * 2547717 * 2
def baseEnd_2547717 : Nat := 436067797543637926406923

theorem tailTrace_2547717 : CollatzResearch.WordTrace tailWord_2547717 prefixEnd_2547717 436067797543637926406923 := by
  unfold tailWord_2547717
  simp only [CollatzResearch.WordTrace]
  refine ⟨92922872911063899267401405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61948581940709266178267603 92922872911063899267401405)
  ·
    refine ⟨34846077341648962225275527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 92922872911063899267401405 34846077341648962225275527)
    ·
      refine ⟨52269116012473443337913291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34846077341648962225275527 52269116012473443337913291)
      ·
        refine ⟨78403674018710165006869937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52269116012473443337913291 78403674018710165006869937)
        ·
          refine ⟨58802755514032623755152453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78403674018710165006869937 58802755514032623755152453)
          ·
            refine ⟨11025516658881116954091085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58802755514032623755152453 11025516658881116954091085)
            ·
              refine ⟨4134568747080418857784157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11025516658881116954091085 4134568747080418857784157)
              ·
                refine ⟨1550463280155157071669059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4134568747080418857784157 1550463280155157071669059)
                ·
                  refine ⟨2325694920232735607503589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550463280155157071669059 2325694920232735607503589)
                  ·
                    refine ⟨436067797543637926406923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2325694920232735607503589 436067797543637926406923)
                    ·
                      rfl

theorem cell23_2547717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 3, 1, 4].length) (baseStart_2547717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547717 prefixEnd_2547717 := by exact prefixLift 2547717
  have htrace : WordTrace (prefixWord ++ tailWord_2547717) baseStart_2547717 baseEnd_2547717 := by
    simpa [prefixWord, tailWord_2547717, baseEnd_2547717] using wordTrace_append hprefix tailTrace_2547717
  have hstable : (prefixWord ++ tailWord_2547717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547717).length < 2 ^ (prefixWord ++ tailWord_2547717).sum := by decide
  have hdescent : baseEnd_2547717 < baseStart_2547717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547743 : List Nat := [1, 1, 2, 4, 1, 2, 2, 2, 3, 5]
def baseStart_2547743 : Nat := 118140960795 + 2547743 * 2 ^ 59
def prefixEnd_2547743 : Nat := 4983230072969 + 3 ^ 40 * 2547743 * 2
def baseEnd_2547743 : Nat := 436072247709310225831883

theorem tailTrace_2547743 : CollatzResearch.WordTrace tailWord_2547743 prefixEnd_2547743 436072247709310225831883 := by
  unfold tailWord_2547743
  simp only [CollatzResearch.WordTrace]
  refine ⟨92923821208969705707847883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61949214139313137138565255 92923821208969705707847883)
  ·
    refine ⟨139385731813454558561771825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92923821208969705707847883 139385731813454558561771825)
    ·
      refine ⟨104539298860090918921328869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139385731813454558561771825 104539298860090918921328869)
      ·
        refine ⟨19601118536267047297749163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 104539298860090918921328869 19601118536267047297749163)
        ·
          refine ⟨29401677804400570946623745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19601118536267047297749163 29401677804400570946623745)
          ·
            refine ⟨22051258353300428209967809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 29401677804400570946623745 22051258353300428209967809)
            ·
              refine ⟨16538443764975321157475857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22051258353300428209967809 16538443764975321157475857)
              ·
                refine ⟨12403832823731490868106893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16538443764975321157475857 12403832823731490868106893)
                ·
                  refine ⟨4651437308899309075540085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12403832823731490868106893 4651437308899309075540085)
                  ·
                    refine ⟨436072247709310225831883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4651437308899309075540085 436072247709310225831883)
                    ·
                      rfl

theorem cell23_2547743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 3, 5].length) (baseStart_2547743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547743 prefixEnd_2547743 := by exact prefixLift 2547743
  have htrace : WordTrace (prefixWord ++ tailWord_2547743) baseStart_2547743 baseEnd_2547743 := by
    simpa [prefixWord, tailWord_2547743, baseEnd_2547743] using wordTrace_append hprefix tailTrace_2547743
  have hstable : (prefixWord ++ tailWord_2547743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547743).length < 2 ^ (prefixWord ++ tailWord_2547743).sum := by decide
  have hdescent : baseEnd_2547743 < baseStart_2547743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547760 : List Nat := [2, 1, 1, 1, 2, 5, 3, 2, 1, 5]
def baseStart_2547760 : Nat := 118140960795 + 2547760 * 2 ^ 59
def prefixEnd_2547760 : Nat := 4983230072969 + 3 ^ 40 * 2547760 * 2
def baseEnd_2547760 : Nat := 436075157433019036994357

theorem tailTrace_2547760 : CollatzResearch.WordTrace tailWord_2547760 prefixEnd_2547760 436075157433019036994357 := by
  unfold tailWord_2547760
  simp only [CollatzResearch.WordTrace]
  refine ⟨46462220624954058805608367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61949627499938745074144489 46462220624954058805608367)
  ·
    refine ⟨69693330937431088208412551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46462220624954058805608367 69693330937431088208412551)
    ·
      refine ⟨104539996406146632312618827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69693330937431088208412551 104539996406146632312618827)
      ·
        refine ⟨156809994609219948468928241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104539996406146632312618827 156809994609219948468928241)
        ·
          refine ⟨117607495956914961351696181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156809994609219948468928241 117607495956914961351696181)
          ·
            refine ⟨11025702745960777626721517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 117607495956914961351696181 11025702745960777626721517)
            ·
              refine ⟨4134638529735291610020569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11025702745960777626721517 4134638529735291610020569)
              ·
                refine ⟨3100978897301468707515427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4134638529735291610020569 3100978897301468707515427)
                ·
                  refine ⟨4651468345952203061273141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3100978897301468707515427 4651468345952203061273141)
                  ·
                    refine ⟨436075157433019036994357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4651468345952203061273141 436075157433019036994357)
                    ·
                      rfl

theorem cell23_2547760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 3, 2, 1, 5].length) (baseStart_2547760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547760 prefixEnd_2547760 := by exact prefixLift 2547760
  have htrace : WordTrace (prefixWord ++ tailWord_2547760) baseStart_2547760 baseEnd_2547760 := by
    simpa [prefixWord, tailWord_2547760, baseEnd_2547760] using wordTrace_append hprefix tailTrace_2547760
  have hstable : (prefixWord ++ tailWord_2547760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547760).length < 2 ^ (prefixWord ++ tailWord_2547760).sum := by decide
  have hdescent : baseEnd_2547760 < baseStart_2547760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547793 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 4]
def baseStart_2547793 : Nat := 118140960795 + 2547793 * 2 ^ 59
def prefixEnd_2547793 : Nat := 4983230072969 + 3 ^ 40 * 2547793 * 2
def baseEnd_2547793 : Nat := 1308242417160655481870419

theorem tailTrace_2547793 : CollatzResearch.WordTrace tailWord_2547793 prefixEnd_2547793 1308242417160655481870419 := by
  unfold tailWord_2547793
  simp only [CollatzResearch.WordTrace]
  refine ⟨92925644858788564247168033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61950429905859042831445355 92925644858788564247168033)
  ·
    refine ⟨69694233644091423185376025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92925644858788564247168033 69694233644091423185376025)
    ·
      refine ⟨52270675233068567389032019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69694233644091423185376025 52270675233068567389032019)
      ·
        refine ⟨78406012849602851083548029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52270675233068567389032019 78406012849602851083548029)
        ·
          refine ⟨29402254818601069156330511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78406012849602851083548029 29402254818601069156330511)
          ·
            refine ⟨44103382227901603734495767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 29402254818601069156330511 44103382227901603734495767)
            ·
              refine ⟨66155073341852405601743651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44103382227901603734495767 66155073341852405601743651)
              ·
                refine ⟨99232610012778608402615477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66155073341852405601743651 99232610012778608402615477)
                ·
                  refine ⟨9303057188697994537745201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 99232610012778608402615477 9303057188697994537745201)
                  ·
                    refine ⟨6977292891523495903308901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9303057188697994537745201 6977292891523495903308901)
                    ·
                      refine ⟨1308242417160655481870419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6977292891523495903308901 1308242417160655481870419)
                      ·
                        rfl

theorem cell23_2547793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 2, 4].length) (baseStart_2547793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547793 prefixEnd_2547793 := by exact prefixLift 2547793
  have htrace : WordTrace (prefixWord ++ tailWord_2547793) baseStart_2547793 baseEnd_2547793 := by
    simpa [prefixWord, tailWord_2547793, baseEnd_2547793] using wordTrace_append hprefix tailTrace_2547793
  have hstable : (prefixWord ++ tailWord_2547793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547793).length < 2 ^ (prefixWord ++ tailWord_2547793).sum := by decide
  have hdescent : baseEnd_2547793 < baseStart_2547793 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547800 : List Nat := [2, 1, 2, 2, 1, 4, 1, 2, 3, 2, 3]
def baseStart_2547800 : Nat := 118140960795 + 2547800 * 2 ^ 59
def prefixEnd_2547800 : Nat := 4983230072969 + 3 ^ 40 * 2547800 * 2
def baseEnd_2547800 : Nat := 1308246011525236954482887

theorem tailTrace_2547800 : CollatzResearch.WordTrace tailWord_2547800 prefixEnd_2547800 1308246011525236954482887 := by
  unfold tailWord_2547800
  simp only [CollatzResearch.WordTrace]
  refine ⟨46462950084881602221336427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61950600113175469628448569 46462950084881602221336427)
  ·
    refine ⟨69694425127322403332004641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46462950084881602221336427 69694425127322403332004641)
    ·
      refine ⟨52270818845491802499003481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69694425127322403332004641 52270818845491802499003481)
      ·
        refine ⟨39203114134118851874252611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 52270818845491802499003481 39203114134118851874252611)
        ·
          refine ⟨58804671201178277811378917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39203114134118851874252611 58804671201178277811378917)
          ·
            refine ⟨11025875850220927089633547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58804671201178277811378917 11025875850220927089633547)
            ·
              refine ⟨16538813775331390634450321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11025875850220927089633547 16538813775331390634450321)
              ·
                refine ⟨12404110331498542975837741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16538813775331390634450321 12404110331498542975837741)
                ·
                  refine ⟨4651541374311953615939153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12404110331498542975837741 4651541374311953615939153)
                  ·
                    refine ⟨3488656030733965211954365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4651541374311953615939153 3488656030733965211954365)
                    ·
                      refine ⟨1308246011525236954482887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3488656030733965211954365 1308246011525236954482887)
                      ·
                        rfl

theorem cell23_2547800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_2547800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547800 prefixEnd_2547800 := by exact prefixLift 2547800
  have htrace : WordTrace (prefixWord ++ tailWord_2547800) baseStart_2547800 baseEnd_2547800 := by
    simpa [prefixWord, tailWord_2547800, baseEnd_2547800] using wordTrace_append hprefix tailTrace_2547800
  have hstable : (prefixWord ++ tailWord_2547800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547800).length < 2 ^ (prefixWord ++ tailWord_2547800).sum := by decide
  have hdescent : baseEnd_2547800 < baseStart_2547800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547820 : List Nat := [2, 2, 1, 1, 3, 4, 3, 7]
def baseStart_2547820 : Nat := 118140960795 + 2547820 * 2 ^ 59
def prefixEnd_2547820 : Nat := 4983230072969 + 3 ^ 40 * 2547820 * 2
def baseEnd_2547820 : Nat := 48453936338456550971585

theorem tailTrace_2547820 : CollatzResearch.WordTrace tailWord_2547820 prefixEnd_2547820 48453936338456550971585 := by
  unfold tailWord_2547820
  simp only [CollatzResearch.WordTrace]
  refine ⟨46463314814845373929200457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61951086419793831905600609 46463314814845373929200457)
  ·
    refine ⟨34847486111134030446900343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46463314814845373929200457 34847486111134030446900343)
    ·
      refine ⟨52271229166701045670350515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34847486111134030446900343 52271229166701045670350515)
      ·
        refine ⟨78406843750051568505525773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52271229166701045670350515 78406843750051568505525773)
        ·
          refine ⟨29402566406269338189572165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 78406843750051568505525773 29402566406269338189572165)
          ·
            refine ⟨5512981201175500910544781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 29402566406269338189572165 5512981201175500910544781)
            ·
              refine ⟨2067367950440812841454293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5512981201175500910544781 2067367950440812841454293)
              ·
                refine ⟨48453936338456550971585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2067367950440812841454293 48453936338456550971585)
                ·
                  rfl

theorem cell23_2547820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 3, 7].length) (baseStart_2547820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547820 prefixEnd_2547820 := by exact prefixLift 2547820
  have htrace : WordTrace (prefixWord ++ tailWord_2547820) baseStart_2547820 baseEnd_2547820 := by
    simpa [prefixWord, tailWord_2547820, baseEnd_2547820] using wordTrace_append hprefix tailTrace_2547820
  have hstable : (prefixWord ++ tailWord_2547820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547820).length < 2 ^ (prefixWord ++ tailWord_2547820).sum := by decide
  have hdescent : baseEnd_2547820 < baseStart_2547820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547831 : List Nat := [1, 1, 3, 1, 1, 6, 2, 3, 1, 2, 2]
def baseStart_2547831 : Nat := 118140960795 + 2547831 * 2 ^ 59
def prefixEnd_2547831 : Nat := 4983230072969 + 3 ^ 40 * 2547831 * 2
def baseEnd_2547831 : Nat := 1308261929425526333195245

theorem tailTrace_2547831 : CollatzResearch.WordTrace tailWord_2547831 prefixEnd_2547831 1308261929425526333195245 := by
  unfold tailWord_2547831
  simp only [CollatzResearch.WordTrace]
  refine ⟨92927030832650896737051347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61951353888433931158034231 92927030832650896737051347)
  ·
    refine ⟨139390546248976345105577021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92927030832650896737051347 139390546248976345105577021)
    ·
      refine ⟨52271454843366129414591383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 139390546248976345105577021 52271454843366129414591383)
      ·
        refine ⟨78407182265049194121887075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52271454843366129414591383 78407182265049194121887075)
        ·
          refine ⟨117610773397573791182830613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78407182265049194121887075 117610773397573791182830613)
          ·
            refine ⟨5513005003011271461695185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 117610773397573791182830613 5513005003011271461695185)
            ·
              refine ⟨4134753752258453596271389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5513005003011271461695185 4134753752258453596271389)
              ·
                refine ⟨1550532657096920098601771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4134753752258453596271389 1550532657096920098601771)
                ·
                  refine ⟨2325798985645380147902657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550532657096920098601771 2325798985645380147902657)
                  ·
                    refine ⟨1744349239234035110926993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2325798985645380147902657 1744349239234035110926993)
                    ·
                      refine ⟨1308261929425526333195245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744349239234035110926993 1308261929425526333195245)
                      ·
                        rfl

theorem cell23_2547831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 3, 1, 2, 2].length) (baseStart_2547831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547831 prefixEnd_2547831 := by exact prefixLift 2547831
  have htrace : WordTrace (prefixWord ++ tailWord_2547831) baseStart_2547831 baseEnd_2547831 := by
    simpa [prefixWord, tailWord_2547831, baseEnd_2547831] using wordTrace_append hprefix tailTrace_2547831
  have hstable : (prefixWord ++ tailWord_2547831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547831).length < 2 ^ (prefixWord ++ tailWord_2547831).sum := by decide
  have hdescent : baseEnd_2547831 < baseStart_2547831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547841 : List Nat := [1, 2, 4, 2, 4, 1, 1, 2, 2, 4]
def baseStart_2547841 : Nat := 118140960795 + 2547841 * 2 ^ 59
def prefixEnd_2547841 : Nat := 4983230072969 + 3 ^ 40 * 2547841 * 2
def baseEnd_2547841 : Nat := 436089021410690431356733

theorem tailTrace_2547841 : CollatzResearch.WordTrace tailWord_2547841 prefixEnd_2547841 436089021410690431356733 := by
  unfold tailWord_2547841
  simp only [CollatzResearch.WordTrace]
  refine ⟨92927395562614668444915377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61951597041743112296610251 92927395562614668444915377)
  ·
    refine ⟨69695546671961001333686533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92927395562614668444915377 69695546671961001333686533)
    ·
      refine ⟨13067915000992687750066225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 69695546671961001333686533 13067915000992687750066225)
      ·
        refine ⟨9800936250744515812549669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13067915000992687750066225 9800936250744515812549669)
        ·
          refine ⟨1837675547014596714853063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9800936250744515812549669 1837675547014596714853063)
          ·
            refine ⟨2756513320521895072279595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837675547014596714853063 2756513320521895072279595)
            ·
              refine ⟨4134769980782842608419393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756513320521895072279595 4134769980782842608419393)
              ·
                refine ⟨3101077485587131956314545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4134769980782842608419393 3101077485587131956314545)
                ·
                  refine ⟨2325808114190348967235909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3101077485587131956314545 2325808114190348967235909)
                  ·
                    refine ⟨436089021410690431356733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2325808114190348967235909 436089021410690431356733)
                    ·
                      rfl

theorem cell23_2547841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_2547841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547841 prefixEnd_2547841 := by exact prefixLift 2547841
  have htrace : WordTrace (prefixWord ++ tailWord_2547841) baseStart_2547841 baseEnd_2547841 := by
    simpa [prefixWord, tailWord_2547841, baseEnd_2547841] using wordTrace_append hprefix tailTrace_2547841
  have hstable : (prefixWord ++ tailWord_2547841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547841).length < 2 ^ (prefixWord ++ tailWord_2547841).sum := by decide
  have hdescent : baseEnd_2547841 < baseStart_2547841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547864 : List Nat := [2, 1, 2, 4, 3, 2, 1, 1, 1, 3, 3]
def baseStart_2547864 : Nat := 118140960795 + 2547864 * 2 ^ 59
def prefixEnd_2547864 : Nat := 4983230072969 + 3 ^ 40 * 2547864 * 2
def baseEnd_2547864 : Nat := 1308278874287124704082593

theorem tailTrace_2547864 : CollatzResearch.WordTrace tailWord_2547864 prefixEnd_2547864 1308278874287124704082593 := by
  unfold tailWord_2547864
  simp only [CollatzResearch.WordTrace]
  refine ⟨46464117220765671686501323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61952156294354228915335097 46464117220765671686501323)
  ·
    refine ⟨69696175831148507529751985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46464117220765671686501323 69696175831148507529751985)
    ·
      refine ⟨52272131873361380647313989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69696175831148507529751985 52272131873361380647313989)
      ·
        refine ⟨9801024726255258871371373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 52272131873361380647313989 9801024726255258871371373)
        ·
          refine ⟨3675384272345722076764265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9801024726255258871371373 3675384272345722076764265)
          ·
            refine ⟨2756538204259291557573199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3675384272345722076764265 2756538204259291557573199)
            ·
              refine ⟨4134807306388937336359799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756538204259291557573199 4134807306388937336359799)
              ·
                refine ⟨6202210959583406004539699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4134807306388937336359799 6202210959583406004539699)
                ·
                  refine ⟨9303316439375109006809549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6202210959583406004539699 9303316439375109006809549)
                  ·
                    refine ⟨3488743664765665877553581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9303316439375109006809549 3488743664765665877553581)
                    ·
                      refine ⟨1308278874287124704082593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3488743664765665877553581 1308278874287124704082593)
                      ·
                        rfl

theorem cell23_2547864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_2547864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547864 prefixEnd_2547864 := by exact prefixLift 2547864
  have htrace : WordTrace (prefixWord ++ tailWord_2547864) baseStart_2547864 baseEnd_2547864 := by
    simpa [prefixWord, tailWord_2547864, baseEnd_2547864] using wordTrace_append hprefix tailTrace_2547864
  have hstable : (prefixWord ++ tailWord_2547864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547864).length < 2 ^ (prefixWord ++ tailWord_2547864).sum := by decide
  have hdescent : baseEnd_2547864 < baseStart_2547864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547882 : List Nat := [3, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2]
def baseStart_2547882 : Nat := 118140960795 + 2547882 * 2 ^ 59
def prefixEnd_2547882 : Nat := 4983230072969 + 3 ^ 40 * 2547882 * 2
def baseEnd_2547882 : Nat := 1308288116938905633657511

theorem tailTrace_2547882 : CollatzResearch.WordTrace tailWord_2547882 prefixEnd_2547882 1308288116938905633657511 := by
  unfold tailWord_2547882
  simp only [CollatzResearch.WordTrace]
  refine ⟨23232222738866533111789475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61952593970310754964771933 23232222738866533111789475)
  ·
    refine ⟨34848334108299799667684213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23232222738866533111789475 34848334108299799667684213)
    ·
      refine ⟨3267031322653106218845395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34848334108299799667684213 3267031322653106218845395)
      ·
        refine ⟨4900546983979659328268093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3267031322653106218845395 4900546983979659328268093)
        ·
          refine ⟨1837705118992372248100535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4900546983979659328268093 1837705118992372248100535)
          ·
            refine ⟨2756557678488558372150803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837705118992372248100535 2756557678488558372150803)
            ·
              refine ⟨4134836517732837558226205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756557678488558372150803 4134836517732837558226205)
              ·
                refine ⟨1550563694149814084334827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4134836517732837558226205 1550563694149814084334827)
                ·
                  refine ⟨2325845541224721126502241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550563694149814084334827 2325845541224721126502241)
                  ·
                    refine ⟨1744384155918540844876681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2325845541224721126502241 1744384155918540844876681)
                    ·
                      refine ⟨1308288116938905633657511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744384155918540844876681 1308288116938905633657511)
                      ·
                        rfl

theorem cell23_2547882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_2547882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547882 prefixEnd_2547882 := by exact prefixLift 2547882
  have htrace : WordTrace (prefixWord ++ tailWord_2547882) baseStart_2547882 baseEnd_2547882 := by
    simpa [prefixWord, tailWord_2547882, baseEnd_2547882] using wordTrace_append hprefix tailTrace_2547882
  have hstable : (prefixWord ++ tailWord_2547882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547882).length < 2 ^ (prefixWord ++ tailWord_2547882).sum := by decide
  have hdescent : baseEnd_2547882 < baseStart_2547882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547890 : List Nat := [3, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5]
def baseStart_2547890 : Nat := 118140960795 + 2547890 * 2 ^ 59
def prefixEnd_2547890 : Nat := 4983230072969 + 3 ^ 40 * 2547890 * 2
def baseEnd_2547890 : Nat := 1308292224784141602357473

theorem tailTrace_2547890 : CollatzResearch.WordTrace tailWord_2547890 prefixEnd_2547890 1308292224784141602357473 := by
  unfold tailWord_2547890
  simp only [CollatzResearch.WordTrace]
  refine ⟨23232295684859287453362281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 61952788492958099875632749 23232295684859287453362281)
  ·
    refine ⟨17424221763644465590021711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23232295684859287453362281 17424221763644465590021711)
    ·
      refine ⟨26136332645466698385032567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17424221763644465590021711 26136332645466698385032567)
      ·
        refine ⟨39204498968200047577548851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26136332645466698385032567 39204498968200047577548851)
        ·
          refine ⟨58806748452300071366323277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39204498968200047577548851 58806748452300071366323277)
          ·
            refine ⟨22052530669612526762371229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 58806748452300071366323277 22052530669612526762371229)
            ·
              refine ⟨8269699001104697535889211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22052530669612526762371229 8269699001104697535889211)
              ·
                refine ⟨12404548501657046303833817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8269699001104697535889211 12404548501657046303833817)
                ·
                  refine ⟨9303411376242784727875363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12404548501657046303833817 9303411376242784727875363)
                  ·
                    refine ⟨13955117064364177091813045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9303411376242784727875363 13955117064364177091813045)
                    ·
                      refine ⟨1308292224784141602357473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 13955117064364177091813045 1308292224784141602357473)
                      ·
                        rfl

theorem cell23_2547890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 3, 1, 2, 1, 5].length) (baseStart_2547890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547890 prefixEnd_2547890 := by exact prefixLift 2547890
  have htrace : WordTrace (prefixWord ++ tailWord_2547890) baseStart_2547890 baseEnd_2547890 := by
    simpa [prefixWord, tailWord_2547890, baseEnd_2547890] using wordTrace_append hprefix tailTrace_2547890
  have hstable : (prefixWord ++ tailWord_2547890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547890).length < 2 ^ (prefixWord ++ tailWord_2547890).sum := by decide
  have hdescent : baseEnd_2547890 < baseStart_2547890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547903 : List Nat := [1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 9]
def baseStart_2547903 : Nat := 118140960795 + 2547903 * 2 ^ 59
def prefixEnd_2547903 : Nat := 4983230072969 + 3 ^ 40 * 2547903 * 2
def baseEnd_2547903 : Nat := 1308298900032650051494913

theorem tailTrace_2547903 : CollatzResearch.WordTrace tailWord_2547903 prefixEnd_2547903 1308298900032650051494913 := by
  unfold tailWord_2547903
  simp only [CollatzResearch.WordTrace]
  refine ⟨92929656888390053033672363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61953104592260035355781575 92929656888390053033672363)
  ·
    refine ⟨139394485332585079550508545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92929656888390053033672363 139394485332585079550508545)
    ·
      refine ⟨104545863999438809662881409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 139394485332585079550508545 104545863999438809662881409)
      ·
        refine ⟨78409397999579107247161057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104545863999438809662881409 78409397999579107247161057)
        ·
          refine ⟨58807048499684330435370793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78409397999579107247161057 58807048499684330435370793)
          ·
            refine ⟨44105286374763247826528095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58807048499684330435370793 44105286374763247826528095)
            ·
              refine ⟨66157929562144871739792143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 44105286374763247826528095 66157929562144871739792143)
              ·
                refine ⟨99236894343217307609688215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66157929562144871739792143 99236894343217307609688215)
                ·
                  refine ⟨148855341514825961414532323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 99236894343217307609688215 148855341514825961414532323)
                  ·
                    refine ⟨223283012272238942121798485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 148855341514825961414532323 223283012272238942121798485)
                    ·
                      refine ⟨1308298900032650051494913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 223283012272238942121798485 1308298900032650051494913)
                      ·
                        rfl

theorem cell23_2547903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_2547903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547903 prefixEnd_2547903 := by exact prefixLift 2547903
  have htrace : WordTrace (prefixWord ++ tailWord_2547903) baseStart_2547903 baseEnd_2547903 := by
    simpa [prefixWord, tailWord_2547903, baseEnd_2547903] using wordTrace_append hprefix tailTrace_2547903
  have hstable : (prefixWord ++ tailWord_2547903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547903).length < 2 ^ (prefixWord ++ tailWord_2547903).sum := by decide
  have hdescent : baseEnd_2547903 < baseStart_2547903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547904 : List Nat := [2, 1, 1, 2, 5, 1, 2, 1, 4, 2, 2]
def baseStart_2547904 : Nat := 118140960795 + 2547904 * 2 ^ 59
def prefixEnd_2547904 : Nat := 4983230072969 + 3 ^ 40 * 2547904 * 2
def baseEnd_2547904 : Nat := 1308299413513304547582409

theorem tailTrace_2547904 : CollatzResearch.WordTrace tailWord_2547904 prefixEnd_2547904 1308299413513304547582409 := by
  unfold tailWord_2547904
  simp only [CollatzResearch.WordTrace]
  refine ⟨46464846680693215102229383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61953128907590953469639177 46464846680693215102229383)
  ·
    refine ⟨69697270021039822653344075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46464846680693215102229383 69697270021039822653344075)
    ·
      refine ⟨104545905031559733980016113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69697270021039822653344075 104545905031559733980016113)
      ·
        refine ⟨78409428773669800485012085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104545905031559733980016113 78409428773669800485012085)
        ·
          refine ⟨7350883947531543795469883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 78409428773669800485012085 7350883947531543795469883)
          ·
            refine ⟨11026325921297315693204825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7350883947531543795469883 11026325921297315693204825)
            ·
              refine ⟨8269744440972986769903619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11026325921297315693204825 8269744440972986769903619)
              ·
                refine ⟨12404616661459480154855429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8269744440972986769903619 12404616661459480154855429)
                ·
                  refine ⟨2325865624023652529035393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12404616661459480154855429 2325865624023652529035393)
                  ·
                    refine ⟨1744399218017739396776545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2325865624023652529035393 1744399218017739396776545)
                    ·
                      refine ⟨1308299413513304547582409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744399218017739396776545 1308299413513304547582409)
                      ·
                        rfl

theorem cell23_2547904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 1, 4, 2, 2].length) (baseStart_2547904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547904 prefixEnd_2547904 := by exact prefixLift 2547904
  have htrace : WordTrace (prefixWord ++ tailWord_2547904) baseStart_2547904 baseEnd_2547904 := by
    simpa [prefixWord, tailWord_2547904, baseEnd_2547904] using wordTrace_append hprefix tailTrace_2547904
  have hstable : (prefixWord ++ tailWord_2547904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547904).length < 2 ^ (prefixWord ++ tailWord_2547904).sum := by decide
  have hdescent : baseEnd_2547904 < baseStart_2547904 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547913 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 8]
def baseStart_2547913 : Nat := 118140960795 + 2547913 * 2 ^ 59
def prefixEnd_2547913 : Nat := 4983230072969 + 3 ^ 40 * 2547913 * 2
def baseEnd_2547913 : Nat := 1308304034839195012369867

theorem tailTrace_2547913 : CollatzResearch.WordTrace tailWord_2547913 prefixEnd_2547913 1308304034839195012369867 := by
  unfold tailWord_2547913
  simp only [CollatzResearch.WordTrace]
  refine ⟨92930021618353824741536393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61953347745569216494357595 92930021618353824741536393)
  ·
    refine ⟨69697516213765368556152295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92930021618353824741536393 69697516213765368556152295)
    ·
      refine ⟨104546274320648052834228443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69697516213765368556152295 104546274320648052834228443)
      ·
        refine ⟨156819411480972079251342665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104546274320648052834228443 156819411480972079251342665)
        ·
          refine ⟨117614558610729059438506999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156819411480972079251342665 117614558610729059438506999)
          ·
            refine ⟨176421837916093589157760499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117614558610729059438506999 176421837916093589157760499)
            ·
              refine ⟨264632756874140383736640749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176421837916093589157760499 264632756874140383736640749)
              ·
                refine ⟨99237283827802643901240281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 264632756874140383736640749 99237283827802643901240281)
                ·
                  refine ⟨74427962870851982925930211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 99237283827802643901240281 74427962870851982925930211)
                  ·
                    refine ⟨111641944306277974388895317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 74427962870851982925930211 111641944306277974388895317)
                    ·
                      refine ⟨1308304034839195012369867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 111641944306277974388895317 1308304034839195012369867)
                      ·
                        rfl

theorem cell23_2547913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 1, 8].length) (baseStart_2547913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547913 prefixEnd_2547913 := by exact prefixLift 2547913
  have htrace : WordTrace (prefixWord ++ tailWord_2547913) baseStart_2547913 baseEnd_2547913 := by
    simpa [prefixWord, tailWord_2547913, baseEnd_2547913] using wordTrace_append hprefix tailTrace_2547913
  have hstable : (prefixWord ++ tailWord_2547913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547913).length < 2 ^ (prefixWord ++ tailWord_2547913).sum := by decide
  have hdescent : baseEnd_2547913 < baseStart_2547913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547921 : List Nat := [1, 2, 2, 1, 2, 2, 6, 1, 2, 2, 2]
def baseStart_2547921 : Nat := 118140960795 + 2547921 * 2 ^ 59
def prefixEnd_2547921 : Nat := 4983230072969 + 3 ^ 40 * 2547921 * 2
def baseEnd_2547921 : Nat := 1308308142684430981069831

theorem tailTrace_2547921 : CollatzResearch.WordTrace tailWord_2547921 prefixEnd_2547921 1308308142684430981069831 := by
  unfold tailWord_2547921
  simp only [CollatzResearch.WordTrace]
  refine ⟨92930313402324842107827617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61953542268216561405218411 92930313402324842107827617)
  ·
    refine ⟨69697735051743631580870713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92930313402324842107827617 69697735051743631580870713)
    ·
      refine ⟨52273301288807723685653035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69697735051743631580870713 52273301288807723685653035)
      ·
        refine ⟨78409951933211585528479553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 52273301288807723685653035 78409951933211585528479553)
        ·
          refine ⟨58807463949908689146359665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78409951933211585528479553 58807463949908689146359665)
          ·
            refine ⟨44105597962431516859769749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58807463949908689146359665 44105597962431516859769749)
            ·
              refine ⟨2067449904488977352801707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 44105597962431516859769749 2067449904488977352801707)
              ·
                refine ⟨3101174856733466029202561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067449904488977352801707 3101174856733466029202561)
                ·
                  refine ⟨2325881142550099521901921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3101174856733466029202561 2325881142550099521901921)
                  ·
                    refine ⟨1744410856912574641426441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2325881142550099521901921 1744410856912574641426441)
                    ·
                      refine ⟨1308308142684430981069831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744410856912574641426441 1308308142684430981069831)
                      ·
                        rfl

theorem cell23_2547921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 6, 1, 2, 2, 2].length) (baseStart_2547921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547921 prefixEnd_2547921 := by exact prefixLift 2547921
  have htrace : WordTrace (prefixWord ++ tailWord_2547921) baseStart_2547921 baseEnd_2547921 := by
    simpa [prefixWord, tailWord_2547921, baseEnd_2547921] using wordTrace_append hprefix tailTrace_2547921
  have hstable : (prefixWord ++ tailWord_2547921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547921).length < 2 ^ (prefixWord ++ tailWord_2547921).sum := by decide
  have hdescent : baseEnd_2547921 < baseStart_2547921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2547977 : List Nat := [1, 2, 1, 1, 3, 4, 1, 1, 1, 6, 2]
def baseStart_2547977 : Nat := 118140960795 + 2547977 * 2 ^ 59
def prefixEnd_2547977 : Nat := 4983230072969 + 3 ^ 40 * 2547977 * 2
def baseEnd_2547977 : Nat := 1308336897601082761969573

theorem tailTrace_2547977 : CollatzResearch.WordTrace tailWord_2547977 prefixEnd_2547977 1308336897601082761969573 := by
  unfold tailWord_2547977
  simp only [CollatzResearch.WordTrace]
  refine ⟨92932355890121963671866185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61954903926747975781244123 92932355890121963671866185)
  ·
    refine ⟨69699266917591472753899639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92932355890121963671866185 69699266917591472753899639)
    ·
      refine ⟨104548900376387209130849459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69699266917591472753899639 104548900376387209130849459)
      ·
        refine ⟨156823350564580813696274189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104548900376387209130849459 156823350564580813696274189)
        ·
          refine ⟨58808756461717805136102821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 156823350564580813696274189 58808756461717805136102821)
          ·
            refine ⟨11026641836572088463019279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 58808756461717805136102821 11026641836572088463019279)
            ·
              refine ⟨16539962754858132694528919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11026641836572088463019279 16539962754858132694528919)
              ·
                refine ⟨24809944132287199041793379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16539962754858132694528919 24809944132287199041793379)
                ·
                  refine ⟨37214916198430798562690069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24809944132287199041793379 37214916198430798562690069)
                  ·
                    refine ⟨1744449196801443682626097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 37214916198430798562690069 1744449196801443682626097)
                    ·
                      refine ⟨1308336897601082761969573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744449196801443682626097 1308336897601082761969573)
                      ·
                        rfl

theorem cell23_2547977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 1, 1, 6, 2].length) (baseStart_2547977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2547977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2547977 prefixEnd_2547977 := by exact prefixLift 2547977
  have htrace : WordTrace (prefixWord ++ tailWord_2547977) baseStart_2547977 baseEnd_2547977 := by
    simpa [prefixWord, tailWord_2547977, baseEnd_2547977] using wordTrace_append hprefix tailTrace_2547977
  have hstable : (prefixWord ++ tailWord_2547977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2547977).length < 2 ^ (prefixWord ++ tailWord_2547977).sum := by decide
  have hdescent : baseEnd_2547977 < baseStart_2547977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2547977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548017 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 8]
def baseStart_2548017 : Nat := 118140960795 + 2548017 * 2 ^ 59
def prefixEnd_2548017 : Nat := 4983230072969 + 3 ^ 40 * 2548017 * 2
def baseEnd_2548017 : Nat := 145373048536362511718821

theorem tailTrace_2548017 : CollatzResearch.WordTrace tailWord_2548017 prefixEnd_2548017 145373048536362511718821 := by
  unfold tailWord_2548017
  simp only [CollatzResearch.WordTrace]
  refine ⟨92933814809977050503322305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61955876539984700335548203 92933814809977050503322305)
  ·
    refine ⟨69700361107482787877491729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92933814809977050503322305 69700361107482787877491729)
    ·
      refine ⟨52275270830612090908118797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 69700361107482787877491729 52275270830612090908118797)
      ·
        refine ⟨19603226561479534090544549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52275270830612090908118797 19603226561479534090544549)
        ·
          refine ⟨3675604980277412641977103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19603226561479534090544549 3675604980277412641977103)
          ·
            refine ⟨5513407470416118962965655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3675604980277412641977103 5513407470416118962965655)
            ·
              refine ⟨8270111205624178444448483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513407470416118962965655 8270111205624178444448483)
              ·
                refine ⟨12405166808436267666672725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8270111205624178444448483 12405166808436267666672725)
                ·
                  refine ⟨145373048536362511718821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 12405166808436267666672725 145373048536362511718821)
                  ·
                    rfl

theorem cell23_2548017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 8].length) (baseStart_2548017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548017 prefixEnd_2548017 := by exact prefixLift 2548017
  have htrace : WordTrace (prefixWord ++ tailWord_2548017) baseStart_2548017 baseEnd_2548017 := by
    simpa [prefixWord, tailWord_2548017, baseEnd_2548017] using wordTrace_append hprefix tailTrace_2548017
  have hstable : (prefixWord ++ tailWord_2548017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548017).length < 2 ^ (prefixWord ++ tailWord_2548017).sum := by decide
  have hdescent : baseEnd_2548017 < baseStart_2548017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548040 : List Nat := [2, 1, 3, 1, 1, 2, 2, 1, 2, 1, 7]
def baseStart_2548040 : Nat := 118140960795 + 2548040 * 2 ^ 59
def prefixEnd_2548040 : Nat := 4983230072969 + 3 ^ 40 * 2548040 * 2
def baseEnd_2548040 : Nat := 1308369246882316015481783

theorem tailTrace_2548040 : CollatzResearch.WordTrace tailWord_2548040 prefixEnd_2548040 1308369246882316015481783 := by
  unfold tailWord_2548040
  simp only [CollatzResearch.WordTrace]
  refine ⟨46467326844446862715704787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61956435792595816954273049 46467326844446862715704787)
  ·
    refine ⟨69700990266670294073557181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46467326844446862715704787 69700990266670294073557181)
    ·
      refine ⟨26137871350001360277583943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69700990266670294073557181 26137871350001360277583943)
      ·
        refine ⟨39206807025002040416375915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26137871350001360277583943 39206807025002040416375915)
        ·
          refine ⟨58810210537503060624563873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 39206807025002040416375915 58810210537503060624563873)
          ·
            refine ⟨44107657903127295468422905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 58810210537503060624563873 44107657903127295468422905)
            ·
              refine ⟨33080743427345471601317179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 44107657903127295468422905 33080743427345471601317179)
              ·
                refine ⟨49621115141018207401975769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 33080743427345471601317179 49621115141018207401975769)
                ·
                  refine ⟨37215836355763655551481827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49621115141018207401975769 37215836355763655551481827)
                  ·
                    refine ⟨55823754533645483327222741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 37215836355763655551481827 55823754533645483327222741)
                    ·
                      refine ⟨1308369246882316015481783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 55823754533645483327222741 1308369246882316015481783)
                      ·
                        rfl

theorem cell23_2548040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 1, 2, 1, 7].length) (baseStart_2548040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548040 prefixEnd_2548040 := by exact prefixLift 2548040
  have htrace : WordTrace (prefixWord ++ tailWord_2548040) baseStart_2548040 baseEnd_2548040 := by
    simpa [prefixWord, tailWord_2548040, baseEnd_2548040] using wordTrace_append hprefix tailTrace_2548040
  have hstable : (prefixWord ++ tailWord_2548040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548040).length < 2 ^ (prefixWord ++ tailWord_2548040).sum := by decide
  have hdescent : baseEnd_2548040 < baseStart_2548040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548044 : List Nat := [2, 2, 1, 3, 2, 1, 1, 4, 3, 1, 3]
def baseStart_2548044 : Nat := 118140960795 + 2548044 * 2 ^ 59
def prefixEnd_2548044 : Nat := 4983230072969 + 3 ^ 40 * 2548044 * 2
def baseEnd_2548044 : Nat := 1308371300804933999831765

theorem tailTrace_2548044 : CollatzResearch.WordTrace tailWord_2548044 prefixEnd_2548044 1308371300804933999831765 := by
  unfold tailWord_2548044
  simp only [CollatzResearch.WordTrace]
  refine ⟨46467399790439617057277593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61956533053919489409703457 46467399790439617057277593)
  ·
    refine ⟨34850549842829712792958195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 46467399790439617057277593 34850549842829712792958195)
    ·
      refine ⟨52275824764244569189437293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34850549842829712792958195 52275824764244569189437293)
      ·
        refine ⟨19603434286591713446038985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 52275824764244569189437293 19603434286591713446038985)
        ·
          refine ⟨14702575714943785084529239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19603434286591713446038985 14702575714943785084529239)
          ·
            refine ⟨22053863572415677626793859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14702575714943785084529239 22053863572415677626793859)
            ·
              refine ⟨33080795358623516440190789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22053863572415677626793859 33080795358623516440190789)
              ·
                refine ⟨6202649129741909332535773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 33080795358623516440190789 6202649129741909332535773)
                ·
                  refine ⟨2325993423653215999700915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6202649129741909332535773 2325993423653215999700915)
                  ·
                    refine ⟨3488990135479823999551373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2325993423653215999700915 3488990135479823999551373)
                    ·
                      refine ⟨1308371300804933999831765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3488990135479823999551373 1308371300804933999831765)
                      ·
                        rfl

theorem cell23_2548044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_2548044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548044 prefixEnd_2548044 := by exact prefixLift 2548044
  have htrace : WordTrace (prefixWord ++ tailWord_2548044) baseStart_2548044 baseEnd_2548044 := by
    simpa [prefixWord, tailWord_2548044, baseEnd_2548044] using wordTrace_append hprefix tailTrace_2548044
  have hstable : (prefixWord ++ tailWord_2548044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548044).length < 2 ^ (prefixWord ++ tailWord_2548044).sum := by decide
  have hdescent : baseEnd_2548044 < baseStart_2548044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548071 : List Nat := [1, 1, 5, 1, 3, 2, 1, 2, 2, 3, 2]
def baseStart_2548071 : Nat := 118140960795 + 2548071 * 2 ^ 59
def prefixEnd_2548071 : Nat := 4983230072969 + 3 ^ 40 * 2548071 * 2
def baseEnd_2548071 : Nat := 1308385164782605394194141

theorem tailTrace_2548071 : CollatzResearch.WordTrace tailWord_2548071 prefixEnd_2548071 1308385164782605394194141 := by
  unfold tailWord_2548071
  simp only [CollatzResearch.WordTrace]
  refine ⟨92935784351781417725788067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61957189567854278483858711 92935784351781417725788067)
  ·
    refine ⟨139403676527672126588682101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92935784351781417725788067 139403676527672126588682101)
    ·
      refine ⟨13069094674469261867688947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 139403676527672126588682101 13069094674469261867688947)
      ·
        refine ⟨19603642011703892801533421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13069094674469261867688947 19603642011703892801533421)
        ·
          refine ⟨7351365754388959800575033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19603642011703892801533421 7351365754388959800575033)
          ·
            refine ⟨5513524315791719850431275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7351365754388959800575033 5513524315791719850431275)
            ·
              refine ⟨8270286473687579775646913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513524315791719850431275 8270286473687579775646913)
              ·
                refine ⟨6202714855265684831735185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8270286473687579775646913 6202714855265684831735185)
                ·
                  refine ⟨4652036141449263623801389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6202714855265684831735185 4652036141449263623801389)
                  ·
                    refine ⟨1744513553043473858925521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4652036141449263623801389 1744513553043473858925521)
                    ·
                      refine ⟨1308385164782605394194141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744513553043473858925521 1308385164782605394194141)
                      ·
                        rfl

theorem cell23_2548071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_2548071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548071 prefixEnd_2548071 := by exact prefixLift 2548071
  have htrace : WordTrace (prefixWord ++ tailWord_2548071) baseStart_2548071 baseEnd_2548071 := by
    simpa [prefixWord, tailWord_2548071, baseEnd_2548071] using wordTrace_append hprefix tailTrace_2548071
  have hstable : (prefixWord ++ tailWord_2548071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548071).length < 2 ^ (prefixWord ++ tailWord_2548071).sum := by decide
  have hdescent : baseEnd_2548071 < baseStart_2548071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548104 : List Nat := [2, 1, 3, 3, 1, 1, 3, 1, 3, 2, 3]
def baseStart_2548104 : Nat := 118140960795 + 2548104 * 2 ^ 59
def prefixEnd_2548104 : Nat := 4983230072969 + 3 ^ 40 * 2548104 * 2
def baseEnd_2548104 : Nat := 1308402109644203765081489

theorem tailTrace_2548104 : CollatzResearch.WordTrace tailWord_2548104 prefixEnd_2548104 1308402109644203765081489 := by
  unfold tailWord_2548104
  simp only [CollatzResearch.WordTrace]
  refine ⟨46468493980330932180869683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 61957991973774576241159577 46468493980330932180869683)
  ·
    refine ⟨69702740970496398271304525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 46468493980330932180869683 69702740970496398271304525)
    ·
      refine ⟨26138527863936149351739197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69702740970496398271304525 26138527863936149351739197)
      ·
        refine ⟨9801947948976056006902199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26138527863936149351739197 9801947948976056006902199)
        ·
          refine ⟨14702921923464084010353299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9801947948976056006902199 14702921923464084010353299)
          ·
            refine ⟨22054382885196126015529949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14702921923464084010353299 22054382885196126015529949)
            ·
              refine ⟨8270393581948547255823731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22054382885196126015529949 8270393581948547255823731)
              ·
                refine ⟨12405590372922820883735597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8270393581948547255823731 12405590372922820883735597)
                ·
                  refine ⟨4652096389846057831400849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12405590372922820883735597 4652096389846057831400849)
                  ·
                    refine ⟨3489072292384543373550637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4652096389846057831400849 3489072292384543373550637)
                    ·
                      refine ⟨1308402109644203765081489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3489072292384543373550637 1308402109644203765081489)
                      ·
                        rfl

theorem cell23_2548104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 3, 1, 3, 2, 3].length) (baseStart_2548104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548104 prefixEnd_2548104 := by exact prefixLift 2548104
  have htrace : WordTrace (prefixWord ++ tailWord_2548104) baseStart_2548104 baseEnd_2548104 := by
    simpa [prefixWord, tailWord_2548104, baseEnd_2548104] using wordTrace_append hprefix tailTrace_2548104
  have hstable : (prefixWord ++ tailWord_2548104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548104).length < 2 ^ (prefixWord ++ tailWord_2548104).sum := by decide
  have hdescent : baseEnd_2548104 < baseStart_2548104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548121 : List Nat := [1, 2, 1, 2, 1, 4, 5, 1, 1, 2, 3]
def baseStart_2548121 : Nat := 118140960795 + 2548121 * 2 ^ 59
def prefixEnd_2548121 : Nat := 4983230072969 + 3 ^ 40 * 2548121 * 2
def baseEnd_2548121 : Nat := 1308410838815330198568911

theorem tailTrace_2548121 : CollatzResearch.WordTrace tailWord_2548121 prefixEnd_2548121 1308410838815330198568911 := by
  unfold tailWord_2548121
  simp only [CollatzResearch.WordTrace]
  refine ⟨92937608001600276265108217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61958405334400184176738811 92937608001600276265108217)
  ·
    refine ⟨69703206001200207198831163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92937608001600276265108217 69703206001200207198831163)
    ·
      refine ⟨104554809001800310798246745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 69703206001200207198831163 104554809001800310798246745)
      ·
        refine ⟨78416106751350233098685059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 104554809001800310798246745 78416106751350233098685059)
        ·
          refine ⟨117624160127025349648027589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78416106751350233098685059 117624160127025349648027589)
          ·
            refine ⟨22054530023817253059005173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 117624160127025349648027589 22054530023817253059005173)
            ·
              refine ⟨2067612189732867474281735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22054530023817253059005173 2067612189732867474281735)
              ·
                refine ⟨3101418284599301211422603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067612189732867474281735 3101418284599301211422603)
                ·
                  refine ⟨4652127426898951817133905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3101418284599301211422603 4652127426898951817133905)
                  ·
                    refine ⟨3489095570174213862850429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4652127426898951817133905 3489095570174213862850429)
                    ·
                      refine ⟨1308410838815330198568911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3489095570174213862850429 1308410838815330198568911)
                      ·
                        rfl

theorem cell23_2548121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 1, 2, 3].length) (baseStart_2548121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548121 prefixEnd_2548121 := by exact prefixLift 2548121
  have htrace : WordTrace (prefixWord ++ tailWord_2548121) baseStart_2548121 baseEnd_2548121 := by
    simpa [prefixWord, tailWord_2548121, baseEnd_2548121] using wordTrace_append hprefix tailTrace_2548121
  have hstable : (prefixWord ++ tailWord_2548121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548121).length < 2 ^ (prefixWord ++ tailWord_2548121).sum := by decide
  have hdescent : baseEnd_2548121 < baseStart_2548121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548129 : List Nat := [1, 2, 3, 5, 2, 1, 2, 2, 1, 1, 3]
def baseStart_2548129 : Nat := 118140960795 + 2548129 * 2 ^ 59
def prefixEnd_2548129 : Nat := 4983230072969 + 3 ^ 40 * 2548129 * 2
def baseEnd_2548129 : Nat := 1308414946660566167268875

theorem tailTrace_2548129 : CollatzResearch.WordTrace tailWord_2548129 prefixEnd_2548129 1308414946660566167268875 := by
  unfold tailWord_2548129
  simp only [CollatzResearch.WordTrace]
  refine ⟨92937899785571293631399441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61958599857047529087599627 92937899785571293631399441)
  ·
    refine ⟨69703424839178470223549581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 92937899785571293631399441 69703424839178470223549581)
    ·
      refine ⟨26138784314691926333831093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 69703424839178470223549581 26138784314691926333831093)
      ·
        refine ⟨2450511029502368093796665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26138784314691926333831093 2450511029502368093796665)
        ·
          refine ⟨1837883272126776070347499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2450511029502368093796665 1837883272126776070347499)
          ·
            refine ⟨2756824908190164105521249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837883272126776070347499 2756824908190164105521249)
            ·
              refine ⟨2067618681142623079140937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2756824908190164105521249 2067618681142623079140937)
              ·
                refine ⟨1550714010856967309355703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2067618681142623079140937 1550714010856967309355703)
                ·
                  refine ⟨2326071016285450964033555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550714010856967309355703 2326071016285450964033555)
                  ·
                    refine ⟨3489106524428176446050333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2326071016285450964033555 3489106524428176446050333)
                    ·
                      refine ⟨1308414946660566167268875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3489106524428176446050333 1308414946660566167268875)
                      ·
                        rfl

theorem cell23_2548129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_2548129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548129 prefixEnd_2548129 := by exact prefixLift 2548129
  have htrace : WordTrace (prefixWord ++ tailWord_2548129) baseStart_2548129 baseEnd_2548129 := by
    simpa [prefixWord, tailWord_2548129, baseEnd_2548129] using wordTrace_append hprefix tailTrace_2548129
  have hstable : (prefixWord ++ tailWord_2548129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548129).length < 2 ^ (prefixWord ++ tailWord_2548129).sum := by decide
  have hdescent : baseEnd_2548129 < baseStart_2548129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548135 : List Nat := [1, 1, 6, 1, 1, 3, 1, 4, 1, 2, 2]
def baseStart_2548135 : Nat := 118140960795 + 2548135 * 2 ^ 59
def prefixEnd_2548135 : Nat := 4983230072969 + 3 ^ 40 * 2548135 * 2
def baseEnd_2548135 : Nat := 1308418027544493143793847

theorem tailTrace_2548135 : CollatzResearch.WordTrace tailWord_2548135 prefixEnd_2548135 1308418027544493143793847 := by
  unfold tailWord_2548135
  simp only [CollatzResearch.WordTrace]
  refine ⟨92938118623549556656117859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61958745749033037770745239 92938118623549556656117859)
  ·
    refine ⟨139407177935324334984176789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 92938118623549556656117859 139407177935324334984176789)
    ·
      refine ⟨6534711465718328202383287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 139407177935324334984176789 6534711465718328202383287)
      ·
        refine ⟨9802067198577492303574931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6534711465718328202383287 9802067198577492303574931)
        ·
          refine ⟨14703100797866238455362397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9802067198577492303574931 14703100797866238455362397)
          ·
            refine ⟨5513662799199839420760899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14703100797866238455362397 5513662799199839420760899)
            ·
              refine ⟨8270494198799759131141349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5513662799199839420760899 8270494198799759131141349)
              ·
                refine ⟨1550717662274954837089003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8270494198799759131141349 1550717662274954837089003)
                ·
                  refine ⟨2326076493412432255633505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1550717662274954837089003 2326076493412432255633505)
                  ·
                    refine ⟨1744557370059324191725129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2326076493412432255633505 1744557370059324191725129)
                    ·
                      refine ⟨1308418027544493143793847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1744557370059324191725129 1308418027544493143793847)
                      ·
                        rfl

theorem cell23_2548135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 4, 1, 2, 2].length) (baseStart_2548135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548135 prefixEnd_2548135 := by exact prefixLift 2548135
  have htrace : WordTrace (prefixWord ++ tailWord_2548135) baseStart_2548135 baseEnd_2548135 := by
    simpa [prefixWord, tailWord_2548135, baseEnd_2548135] using wordTrace_append hprefix tailTrace_2548135
  have hstable : (prefixWord ++ tailWord_2548135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548135).length < 2 ^ (prefixWord ++ tailWord_2548135).sum := by decide
  have hdescent : baseEnd_2548135 < baseStart_2548135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2548141 : List Nat := [1, 5, 2, 2, 2, 2, 1, 8]
def baseStart_2548141 : Nat := 118140960795 + 2548141 * 2 ^ 59
def prefixEnd_2548141 : Nat := 4983230072969 + 3 ^ 40 * 2548141 * 2
def baseEnd_2548141 : Nat := 48460041052904448900697

theorem tailTrace_2548141 : CollatzResearch.WordTrace tailWord_2548141 prefixEnd_2548141 48460041052904448900697 := by
  unfold tailWord_2548141
  simp only [CollatzResearch.WordTrace]
  refine ⟨92938337461527819680836277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 61958891641018546453890851 92938337461527819680836277)
  ·
    refine ⟨8712969137018233095078401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 92938337461527819680836277 8712969137018233095078401)
    ·
      refine ⟨6534726852763674821308801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8712969137018233095078401 6534726852763674821308801)
      ·
        refine ⟨4901045139572756115981601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6534726852763674821308801 4901045139572756115981601)
        ·
          refine ⟨3675783854679567086986201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4901045139572756115981601 3675783854679567086986201)
          ·
            refine ⟨2756837891009675315239651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3675783854679567086986201 2756837891009675315239651)
            ·
              refine ⟨4135256836514512972859477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2756837891009675315239651 4135256836514512972859477)
              ·
                refine ⟨48460041052904448900697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4135256836514512972859477 48460041052904448900697)
                ·
                  rfl

theorem cell23_2548141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 1, 8].length) (baseStart_2548141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2548141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2548141 prefixEnd_2548141 := by exact prefixLift 2548141
  have htrace : WordTrace (prefixWord ++ tailWord_2548141) baseStart_2548141 baseEnd_2548141 := by
    simpa [prefixWord, tailWord_2548141, baseEnd_2548141] using wordTrace_append hprefix tailTrace_2548141
  have hstable : (prefixWord ++ tailWord_2548141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2548141).length < 2 ^ (prefixWord ++ tailWord_2548141).sum := by decide
  have hdescent : baseEnd_2548141 < baseStart_2548141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2548141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
