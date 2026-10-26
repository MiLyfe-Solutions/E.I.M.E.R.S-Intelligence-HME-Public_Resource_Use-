import V185TrunkScan22Chunk191

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1711860 : List Nat := [2, 6, 1, 1, 1, 1, 3, 2, 5]
def baseStart_1711860 : Nat := 118140960795 + 1711860 * 2 ^ 59
def prefixEnd_1711860 : Nat := 4983230072969 + 3 ^ 40 * 1711860 * 2
def baseEnd_1711860 : Nat := 195334887379061683017179

theorem tailTrace_1711860 : CollatzResearch.WordTrace tailWord_1711860 prefixEnd_1711860 195334887379061683017179 := by
  unfold tailWord_1711860
  simp only [CollatzResearch.WordTrace]
  refine ⟨31218331789115528628474517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41624442385487371504632689 31218331789115528628474517)
  ·
    refine ⟨1463359302614790404459743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31218331789115528628474517 1463359302614790404459743)
    ·
      refine ⟨2195038953922185606689615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1463359302614790404459743 2195038953922185606689615)
      ·
        refine ⟨3292558430883278410034423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195038953922185606689615 3292558430883278410034423)
        ·
          refine ⟨4938837646324917615051635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3292558430883278410034423 4938837646324917615051635)
          ·
            refine ⟨7408256469487376422577453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4938837646324917615051635 7408256469487376422577453)
            ·
              refine ⟨2778096176057766158466545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7408256469487376422577453 2778096176057766158466545)
              ·
                refine ⟨2083572132043324618849909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778096176057766158466545 2083572132043324618849909)
                ·
                  refine ⟨195334887379061683017179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2083572132043324618849909 195334887379061683017179)
                  ·
                    rfl

theorem cell22_1711860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_1711860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711860 prefixEnd_1711860 := by exact prefixLift 1711860
  have htrace : WordTrace (prefixWord ++ tailWord_1711860) baseStart_1711860 baseEnd_1711860 := by
    simpa [prefixWord, tailWord_1711860, baseEnd_1711860] using wordTrace_append hprefix tailTrace_1711860
  have hstable : (prefixWord ++ tailWord_1711860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711860).length < 2 ^ (prefixWord ++ tailWord_1711860).sum := by decide
  have hdescent : baseEnd_1711860 < baseStart_1711860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711871 : List Nat := [1, 1, 2, 2, 1, 3, 4, 4, 4]
def baseStart_1711871 : Nat := 118140960795 + 1711871 * 2 ^ 59
def prefixEnd_1711871 : Nat := 4983230072969 + 3 ^ 40 * 1711871 * 2
def baseEnd_1711871 : Nat := 195336142553994895675501

theorem tailTrace_1711871 : CollatzResearch.WordTrace tailWord_1711871 prefixEnd_1711871 195336142553994895675501 := by
  unfold tailWord_1711871
  simp only [CollatzResearch.WordTrace]
  refine ⟨62437064781191206135599467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41624709854127470757066311 62437064781191206135599467)
  ·
    refine ⟨93655597171786809203399201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62437064781191206135599467 93655597171786809203399201)
    ·
      refine ⟨70241697878840106902549401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93655597171786809203399201 70241697878840106902549401)
      ·
        refine ⟨52681273409130080176912051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70241697878840106902549401 52681273409130080176912051)
        ·
          refine ⟨79021910113695120265368077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52681273409130080176912051 79021910113695120265368077)
          ·
            refine ⟨29633216292635670099513029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79021910113695120265368077 29633216292635670099513029)
            ·
              refine ⟨5556228054869188143658693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29633216292635670099513029 5556228054869188143658693)
              ·
                refine ⟨1041792760287972776936005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5556228054869188143658693 1041792760287972776936005)
                ·
                  refine ⟨195336142553994895675501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1041792760287972776936005 195336142553994895675501)
                  ·
                    rfl

theorem cell22_1711871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 4, 4, 4].length) (baseStart_1711871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711871 prefixEnd_1711871 := by exact prefixLift 1711871
  have htrace : WordTrace (prefixWord ++ tailWord_1711871) baseStart_1711871 baseEnd_1711871 := by
    simpa [prefixWord, tailWord_1711871, baseEnd_1711871] using wordTrace_append hprefix tailTrace_1711871
  have hstable : (prefixWord ++ tailWord_1711871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711871).length < 2 ^ (prefixWord ++ tailWord_1711871).sum := by decide
  have hdescent : baseEnd_1711871 < baseStart_1711871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711884 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 1, 6]
def baseStart_1711884 : Nat := 118140960795 + 1711884 * 2 ^ 59
def prefixEnd_1711884 : Nat := 4983230072969 + 3 ^ 40 * 1711884 * 2
def baseEnd_1711884 : Nat := 586012877827656986451463

theorem tailTrace_1711884 : CollatzResearch.WordTrace tailWord_1711884 prefixEnd_1711884 586012877827656986451463 := by
  unfold tailWord_1711884
  simp only [CollatzResearch.WordTrace]
  refine ⟨31218769465072054677911353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41625025953429406237215137 31218769465072054677911353)
  ·
    refine ⟨23414077098804041008433515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31218769465072054677911353 23414077098804041008433515)
    ·
      refine ⟨35121115648206061512650273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23414077098804041008433515 35121115648206061512650273)
      ·
        refine ⟨26340836736154546134487705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35121115648206061512650273 26340836736154546134487705)
        ·
          refine ⟨19755627552115909600865779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26340836736154546134487705 19755627552115909600865779)
          ·
            refine ⟨29633441328173864401298669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19755627552115909600865779 29633441328173864401298669)
            ·
              refine ⟨11112540498065199150487001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29633441328173864401298669 11112540498065199150487001)
              ·
                refine ⟨8334405373548899362865251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11112540498065199150487001 8334405373548899362865251)
                ·
                  refine ⟨12501608060323349044297877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8334405373548899362865251 12501608060323349044297877)
                  ·
                    refine ⟨586012877827656986451463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12501608060323349044297877 586012877827656986451463)
                    ·
                      rfl

theorem cell22_1711884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 1, 6].length) (baseStart_1711884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711884 prefixEnd_1711884 := by exact prefixLift 1711884
  have htrace : WordTrace (prefixWord ++ tailWord_1711884) baseStart_1711884 baseEnd_1711884 := by
    simpa [prefixWord, tailWord_1711884, baseEnd_1711884] using wordTrace_append hprefix tailTrace_1711884
  have hstable : (prefixWord ++ tailWord_1711884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711884).length < 2 ^ (prefixWord ++ tailWord_1711884).sum := by decide
  have hdescent : baseEnd_1711884 < baseStart_1711884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711886 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1711886 : Nat := 118140960795 + 1711886 * 2 ^ 59
def prefixEnd_1711886 : Nat := 4983230072969 + 3 ^ 40 * 1711886 * 2
def baseEnd_1711886 : Nat := 586013562468529647901457

theorem tailTrace_1711886 : CollatzResearch.WordTrace tailWord_1711886 prefixEnd_1711886 586013562468529647901457 := by
  unfold tailWord_1711886
  simp only [CollatzResearch.WordTrace]
  refine ⟨7804701484517107962174439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41625074584091242464930341 7804701484517107962174439)
  ·
    refine ⟨11707052226775661943261659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7804701484517107962174439 11707052226775661943261659)
    ·
      refine ⟨17560578340163492914892489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11707052226775661943261659 17560578340163492914892489)
      ·
        refine ⟨13170433755122619686169367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17560578340163492914892489 13170433755122619686169367)
        ·
          refine ⟨19755650632683929529254051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13170433755122619686169367 19755650632683929529254051)
          ·
            refine ⟨29633475949025894293881077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19755650632683929529254051 29633475949025894293881077)
            ·
              refine ⟨2778138370221177590051351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29633475949025894293881077 2778138370221177590051351)
              ·
                refine ⟨4167207555331766385077027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778138370221177590051351 4167207555331766385077027)
                ·
                  refine ⟨6250811332997649577615541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167207555331766385077027 6250811332997649577615541)
                  ·
                    refine ⟨586013562468529647901457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6250811332997649577615541 586013562468529647901457)
                    ·
                      rfl

theorem cell22_1711886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1711886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711886 prefixEnd_1711886 := by exact prefixLift 1711886
  have htrace : WordTrace (prefixWord ++ tailWord_1711886) baseStart_1711886 baseEnd_1711886 := by
    simpa [prefixWord, tailWord_1711886, baseEnd_1711886] using wordTrace_append hprefix tailTrace_1711886
  have hstable : (prefixWord ++ tailWord_1711886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711886).length < 2 ^ (prefixWord ++ tailWord_1711886).sum := by decide
  have hdescent : baseEnd_1711886 < baseStart_1711886 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711890 : List Nat := [3, 2, 4, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1711890 : Nat := 118140960795 + 1711890 * 2 ^ 59
def prefixEnd_1711890 : Nat := 4983230072969 + 3 ^ 40 * 1711890 * 2
def baseEnd_1711890 : Nat := 586014931750274970801445

theorem tailTrace_1711890 : CollatzResearch.WordTrace tailWord_1711890 prefixEnd_1711890 586014931750274970801445 := by
  unfold tailWord_1711890
  simp only [CollatzResearch.WordTrace]
  refine ⟨15609439442030593095135281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41625171845414914920360749 15609439442030593095135281)
  ·
    refine ⟨11707079581522944821351461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15609439442030593095135281 11707079581522944821351461)
    ·
      refine ⟨2195077421535552154003399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11707079581522944821351461 2195077421535552154003399)
      ·
        refine ⟨3292616132303328231005099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2195077421535552154003399 3292616132303328231005099)
        ·
          refine ⟨4938924198454992346507649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3292616132303328231005099 4938924198454992346507649)
          ·
            refine ⟨3704193148841244259880737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4938924198454992346507649 3704193148841244259880737)
            ·
              refine ⟨2778144861630933194910553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3704193148841244259880737 2778144861630933194910553)
              ·
                refine ⟨2083608646223199896182915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2778144861630933194910553 2083608646223199896182915)
                ·
                  refine ⟨3125412969334799844274373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2083608646223199896182915 3125412969334799844274373)
                  ·
                    refine ⟨586014931750274970801445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3125412969334799844274373 586014931750274970801445)
                    ·
                      rfl

theorem cell22_1711890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1711890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711890 prefixEnd_1711890 := by exact prefixLift 1711890
  have htrace : WordTrace (prefixWord ++ tailWord_1711890) baseStart_1711890 baseEnd_1711890 := by
    simpa [prefixWord, tailWord_1711890, baseEnd_1711890] using wordTrace_append hprefix tailTrace_1711890
  have hstable : (prefixWord ++ tailWord_1711890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711890).length < 2 ^ (prefixWord ++ tailWord_1711890).sum := by decide
  have hdescent : baseEnd_1711890 < baseStart_1711890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711976 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 2, 5]
def baseStart_1711976 : Nat := 118140960795 + 1711976 * 2 ^ 59
def prefixEnd_1711976 : Nat := 4983230072969 + 3 ^ 40 * 1711976 * 2
def baseEnd_1711976 : Nat := 586044371307799413151181

theorem tailTrace_1711976 : CollatzResearch.WordTrace tailWord_1711976 prefixEnd_1711976 586044371307799413151181 := by
  unfold tailWord_1711976
  simp only [CollatzResearch.WordTrace]
  refine ⟨31220447222905404534085891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41627262963873872712114521 31220447222905404534085891)
  ·
    refine ⟨46830670834358106801128837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31220447222905404534085891 46830670834358106801128837)
    ·
      refine ⟨8780750781442145025211657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46830670834358106801128837 8780750781442145025211657)
      ·
        refine ⟨6585563086081608768908743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8780750781442145025211657 6585563086081608768908743)
        ·
          refine ⟨9878344629122413153363115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6585563086081608768908743 9878344629122413153363115)
          ·
            refine ⟨14817516943683619730044673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9878344629122413153363115 14817516943683619730044673)
            ·
              refine ⟨11113137707762714797533505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14817516943683619730044673 11113137707762714797533505)
              ·
                refine ⟨8334853280822036098150129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11113137707762714797533505 8334853280822036098150129)
                ·
                  refine ⟨6251139960616527073612597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8334853280822036098150129 6251139960616527073612597)
                  ·
                    refine ⟨586044371307799413151181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6251139960616527073612597 586044371307799413151181)
                    ·
                      rfl

theorem cell22_1711976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_1711976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711976 prefixEnd_1711976 := by exact prefixLift 1711976
  have htrace : WordTrace (prefixWord ++ tailWord_1711976) baseStart_1711976 baseEnd_1711976 := by
    simpa [prefixWord, tailWord_1711976, baseEnd_1711976] using wordTrace_append hprefix tailTrace_1711976
  have hstable : (prefixWord ++ tailWord_1711976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711976).length < 2 ^ (prefixWord ++ tailWord_1711976).sum := by decide
  have hdescent : baseEnd_1711976 < baseStart_1711976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1711982 : List Nat := [4, 1, 2, 3, 1, 2, 1, 4, 1, 3]
def baseStart_1711982 : Nat := 118140960795 + 1711982 * 2 ^ 59
def prefixEnd_1711982 : Nat := 4983230072969 + 3 ^ 40 * 1711982 * 2
def baseEnd_1711982 : Nat := 586046425230417397501163

theorem tailTrace_1711982 : CollatzResearch.WordTrace tailWord_1711982 prefixEnd_1711982 586046425230417397501163 := by
  unfold tailWord_1711982
  simp only [CollatzResearch.WordTrace]
  refine ⟨7805139160473634011611275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41627408855859381395260133 7805139160473634011611275)
  ·
    refine ⟨11707708740710451017416913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7805139160473634011611275 11707708740710451017416913)
    ·
      refine ⟨8780781555532838263062685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11707708740710451017416913 8780781555532838263062685)
      ·
        refine ⟨3292793083324814348648507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8780781555532838263062685 3292793083324814348648507)
        ·
          refine ⟨4939189624987221522972761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3292793083324814348648507 4939189624987221522972761)
          ·
            refine ⟨3704392218740416142229571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4939189624987221522972761 3704392218740416142229571)
            ·
              refine ⟨5556588328110624213344357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3704392218740416142229571 5556588328110624213344357)
              ·
                refine ⟨1041860311520742040002067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5556588328110624213344357 1041860311520742040002067)
                ·
                  refine ⟨1562790467281113060003101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041860311520742040002067 1562790467281113060003101)
                  ·
                    refine ⟨586046425230417397501163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562790467281113060003101 586046425230417397501163)
                    ·
                      rfl

theorem cell22_1711982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 4, 1, 3].length) (baseStart_1711982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1711982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1711982 prefixEnd_1711982 := by exact prefixLift 1711982
  have htrace : WordTrace (prefixWord ++ tailWord_1711982) baseStart_1711982 baseEnd_1711982 := by
    simpa [prefixWord, tailWord_1711982, baseEnd_1711982] using wordTrace_append hprefix tailTrace_1711982
  have hstable : (prefixWord ++ tailWord_1711982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1711982).length < 2 ^ (prefixWord ++ tailWord_1711982).sum := by decide
  have hdescent : baseEnd_1711982 < baseStart_1711982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1711982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712021 : List Nat := [1, 3, 2, 1, 1, 3, 1, 4, 1, 5]
def baseStart_1712021 : Nat := 118140960795 + 1712021 * 2 ^ 59
def prefixEnd_1712021 : Nat := 4983230072969 + 3 ^ 40 * 1712021 * 2
def baseEnd_1712021 : Nat := 586059775727434295776043

theorem tailTrace_1712021 : CollatzResearch.WordTrace tailWord_1712021 prefixEnd_1712021 586059775727434295776043 := by
  unfold tailWord_1712021
  simp only [CollatzResearch.WordTrace]
  refine ⟨62442535730647781753559917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41628357153765187835706611 62442535730647781753559917)
  ·
    refine ⟨23415950898992918157584969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62442535730647781753559917 23415950898992918157584969)
    ·
      refine ⟨17561963174244688618188727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23415950898992918157584969 17561963174244688618188727)
      ·
        refine ⟨26342944761367032927283091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17561963174244688618188727 26342944761367032927283091)
        ·
          refine ⟨39514417142050549390924637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26342944761367032927283091 39514417142050549390924637)
          ·
            refine ⟨14817906428268956021596739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39514417142050549390924637 14817906428268956021596739)
            ·
              refine ⟨22226859642403434032395109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14817906428268956021596739 22226859642403434032395109)
              ·
                refine ⟨4167536182950643881074083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22226859642403434032395109 4167536182950643881074083)
                ·
                  refine ⟨6251304274425965821611125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4167536182950643881074083 6251304274425965821611125)
                  ·
                    refine ⟨586059775727434295776043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6251304274425965821611125 586059775727434295776043)
                    ·
                      rfl

theorem cell22_1712021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 1, 4, 1, 5].length) (baseStart_1712021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712021 prefixEnd_1712021 := by exact prefixLift 1712021
  have htrace : WordTrace (prefixWord ++ tailWord_1712021) baseStart_1712021 baseEnd_1712021 := by
    simpa [prefixWord, tailWord_1712021, baseEnd_1712021] using wordTrace_append hprefix tailTrace_1712021
  have hstable : (prefixWord ++ tailWord_1712021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712021).length < 2 ^ (prefixWord ++ tailWord_1712021).sum := by decide
  have hdescent : baseEnd_1712021 < baseStart_1712021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712023 : List Nat := [1, 1, 3, 3, 1, 3, 1, 5, 4]
def baseStart_1712023 : Nat := 118140960795 + 1712023 * 2 ^ 59
def prefixEnd_1712023 : Nat := 4983230072969 + 3 ^ 40 * 1712023 * 2
def baseEnd_1712023 : Nat := 195353486789435652408679

theorem tailTrace_1712023 : CollatzResearch.WordTrace tailWord_1712023 prefixEnd_1712023 195353486789435652408679 := by
  unfold tailWord_1712023
  simp only [CollatzResearch.WordTrace]
  refine ⟨62442608676640536095132723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41628405784427024063421815 62442608676640536095132723)
  ·
    refine ⟨93663913014960804142699085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62442608676640536095132723 93663913014960804142699085)
    ·
      refine ⟨35123967380610301553512157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93663913014960804142699085 35123967380610301553512157)
      ·
        refine ⟨13171487767728863082567059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35123967380610301553512157 13171487767728863082567059)
        ·
          refine ⟨19757231651593294623850589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13171487767728863082567059 19757231651593294623850589)
          ·
            refine ⟨7408961869347485483943971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19757231651593294623850589 7408961869347485483943971)
            ·
              refine ⟨11113442804021228225915957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7408961869347485483943971 11113442804021228225915957)
              ·
                refine ⟨1041885262876990146179621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11113442804021228225915957 1041885262876990146179621)
                ·
                  refine ⟨195353486789435652408679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1041885262876990146179621 195353486789435652408679)
                  ·
                    rfl

theorem cell22_1712023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 5, 4].length) (baseStart_1712023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712023 prefixEnd_1712023 := by exact prefixLift 1712023
  have htrace : WordTrace (prefixWord ++ tailWord_1712023) baseStart_1712023 baseEnd_1712023 := by
    simpa [prefixWord, tailWord_1712023, baseEnd_1712023] using wordTrace_append hprefix tailTrace_1712023
  have hstable : (prefixWord ++ tailWord_1712023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712023).length < 2 ^ (prefixWord ++ tailWord_1712023).sum := by decide
  have hdescent : baseEnd_1712023 < baseStart_1712023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712111 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 1, 7]
def baseStart_1712111 : Nat := 118140960795 + 1712111 * 2 ^ 59
def prefixEnd_1712111 : Nat := 4983230072969 + 3 ^ 40 * 1712111 * 2
def baseEnd_1712111 : Nat := 586090584566704061025767

theorem tailTrace_1712111 : CollatzResearch.WordTrace tailWord_1712111 prefixEnd_1712111 586090584566704061025767 := by
  unfold tailWord_1712111
  simp only [CollatzResearch.WordTrace]
  refine ⟨62445818300321727124336187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41630545533547818082890791 62445818300321727124336187)
  ·
    refine ⟨93668727450482590686504281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62445818300321727124336187 93668727450482590686504281)
    ·
      refine ⟨70251545587861943014878211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93668727450482590686504281 70251545587861943014878211)
      ·
        refine ⟨105377318381792914522317317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70251545587861943014878211 105377318381792914522317317)
        ·
          refine ⟨19758247196586171472934497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105377318381792914522317317 19758247196586171472934497)
          ·
            refine ⟨14818685397439628604700873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19758247196586171472934497 14818685397439628604700873)
            ·
              refine ⟨11114014048079721453525655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14818685397439628604700873 11114014048079721453525655)
              ·
                refine ⟨16671021072119582180288483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11114014048079721453525655 16671021072119582180288483)
                ·
                  refine ⟨25006531608179373270432725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16671021072119582180288483 25006531608179373270432725)
                  ·
                    refine ⟨586090584566704061025767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25006531608179373270432725 586090584566704061025767)
                    ·
                      rfl

theorem cell22_1712111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 7].length) (baseStart_1712111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712111 prefixEnd_1712111 := by exact prefixLift 1712111
  have htrace : WordTrace (prefixWord ++ tailWord_1712111) baseStart_1712111 baseEnd_1712111 := by
    simpa [prefixWord, tailWord_1712111, baseEnd_1712111] using wordTrace_append hprefix tailTrace_1712111
  have hstable : (prefixWord ++ tailWord_1712111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712111).length < 2 ^ (prefixWord ++ tailWord_1712111).sum := by decide
  have hdescent : baseEnd_1712111 < baseStart_1712111 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712151 : List Nat := [1, 1, 3, 5, 2, 2, 2, 2, 1, 3]
def baseStart_1712151 : Nat := 118140960795 + 1712151 * 2 ^ 59
def prefixEnd_1712151 : Nat := 4983230072969 + 3 ^ 40 * 1712151 * 2
def baseEnd_1712151 : Nat := 586104277384157290025645

theorem tailTrace_1712151 : CollatzResearch.WordTrace tailWord_1712151 prefixEnd_1712151 586104277384157290025645 := by
  unfold tailWord_1712151
  simp only [CollatzResearch.WordTrace]
  refine ⟨62447277220176813955792307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41631518146784542637194871 62447277220176813955792307)
  ·
    refine ⟨93670915830265220933688461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62447277220176813955792307 93670915830265220933688461)
    ·
      refine ⟨35126593436349457850133173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93670915830265220933688461 35126593436349457850133173)
      ·
        refine ⟨3293118134657761673449985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35126593436349457850133173 3293118134657761673449985)
        ·
          refine ⟨2469838600993321255087489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3293118134657761673449985 2469838600993321255087489)
          ·
            refine ⟨1852378950744990941315617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2469838600993321255087489 1852378950744990941315617)
            ·
              refine ⟨1389284213058743205986713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1852378950744990941315617 1389284213058743205986713)
              ·
                refine ⟨1041963159794057404490035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1389284213058743205986713 1041963159794057404490035)
                ·
                  refine ⟨1562944739691086106735053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1041963159794057404490035 1562944739691086106735053)
                  ·
                    refine ⟨586104277384157290025645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1562944739691086106735053 586104277384157290025645)
                    ·
                      rfl

theorem cell22_1712151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 2, 2, 1, 3].length) (baseStart_1712151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712151 prefixEnd_1712151 := by exact prefixLift 1712151
  have htrace : WordTrace (prefixWord ++ tailWord_1712151) baseStart_1712151 baseEnd_1712151 := by
    simpa [prefixWord, tailWord_1712151, baseEnd_1712151] using wordTrace_append hprefix tailTrace_1712151
  have hstable : (prefixWord ++ tailWord_1712151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712151).length < 2 ^ (prefixWord ++ tailWord_1712151).sum := by decide
  have hdescent : baseEnd_1712151 < baseStart_1712151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712188 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 1, 6]
def baseStart_1712188 : Nat := 118140960795 + 1712188 * 2 ^ 59
def prefixEnd_1712188 : Nat := 4983230072969 + 3 ^ 40 * 1712188 * 2
def baseEnd_1712188 : Nat := 586116943240301526850531

theorem tailTrace_1712188 : CollatzResearch.WordTrace tailWord_1712188 prefixEnd_1712188 586116943240301526850531 := by
  unfold tailWord_1712188
  simp only [CollatzResearch.WordTrace]
  refine ⟨31224313360521384637444609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41632417814028512849926145 31224313360521384637444609)
  ·
    refine ⟨23418235020391038478083457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31224313360521384637444609 23418235020391038478083457)
    ·
      refine ⟨17563676265293278858562593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23418235020391038478083457 17563676265293278858562593)
      ·
        refine ⟨13172757198969959143921945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17563676265293278858562593 13172757198969959143921945)
        ·
          refine ⟨9879567899227469357941459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13172757198969959143921945 9879567899227469357941459)
          ·
            refine ⟨14819351848841204036912189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9879567899227469357941459 14819351848841204036912189)
            ·
              refine ⟨5557256943315451513842071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14819351848841204036912189 5557256943315451513842071)
              ·
                refine ⟨8335885414973177270763107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5557256943315451513842071 8335885414973177270763107)
                ·
                  refine ⟨12503828122459765906144661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8335885414973177270763107 12503828122459765906144661)
                  ·
                    refine ⟨586116943240301526850531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12503828122459765906144661 586116943240301526850531)
                    ·
                      rfl

theorem cell22_1712188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_1712188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712188 prefixEnd_1712188 := by exact prefixLift 1712188
  have htrace : WordTrace (prefixWord ++ tailWord_1712188) baseStart_1712188 baseEnd_1712188 := by
    simpa [prefixWord, tailWord_1712188, baseEnd_1712188] using wordTrace_append hprefix tailTrace_1712188
  have hstable : (prefixWord ++ tailWord_1712188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712188).length < 2 ^ (prefixWord ++ tailWord_1712188).sum := by decide
  have hdescent : baseEnd_1712188 < baseStart_1712188 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712205 : List Nat := [1, 6, 1, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1712205 : Nat := 118140960795 + 1712205 * 2 ^ 59
def prefixEnd_1712205 : Nat := 4983230072969 + 3 ^ 40 * 1712205 * 2
def baseEnd_1712205 : Nat := 586122762687719149175479

theorem tailTrace_1712205 : CollatzResearch.WordTrace tailWord_1712205 prefixEnd_1712205 586122762687719149175479 := by
  unfold tailWord_1712205
  simp only [CollatzResearch.WordTrace]
  refine ⟨62449246761981181178258069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41632831174654120785505379 62449246761981181178258069)
  ·
    refine ⟨2927308441967867867730847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62449246761981181178258069 2927308441967867867730847)
    ·
      refine ⟨4390962662951801801596271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2927308441967867867730847 4390962662951801801596271)
      ·
        refine ⟨6586443994427702702394407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4390962662951801801596271 6586443994427702702394407)
        ·
          refine ⟨9879665991641554053591611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6586443994427702702394407 9879665991641554053591611)
          ·
            refine ⟨14819498987462331080387417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9879665991641554053591611 14819498987462331080387417)
            ·
              refine ⟨11114624240596748310290563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14819498987462331080387417 11114624240596748310290563)
              ·
                refine ⟨16671936360895122465435845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11114624240596748310290563 16671936360895122465435845)
                ·
                  refine ⟨3125988067667835462269221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16671936360895122465435845 3125988067667835462269221)
                  ·
                    refine ⟨586122762687719149175479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3125988067667835462269221 586122762687719149175479)
                    ·
                      rfl

theorem cell22_1712205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1712205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712205 prefixEnd_1712205 := by exact prefixLift 1712205
  have htrace : WordTrace (prefixWord ++ tailWord_1712205) baseStart_1712205 baseEnd_1712205 := by
    simpa [prefixWord, tailWord_1712205, baseEnd_1712205] using wordTrace_append hprefix tailTrace_1712205
  have hstable : (prefixWord ++ tailWord_1712205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712205).length < 2 ^ (prefixWord ++ tailWord_1712205).sum := by decide
  have hdescent : baseEnd_1712205 < baseStart_1712205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712263 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1712263 : Nat := 118140960795 + 1712263 * 2 ^ 59
def prefixEnd_1712263 : Nat := 4983230072969 + 3 ^ 40 * 1712263 * 2
def baseEnd_1712263 : Nat := 586142617273026331225301

theorem tailTrace_1712263 : CollatzResearch.WordTrace tailWord_1712263 prefixEnd_1712263 586142617273026331225301 := by
  unfold tailWord_1712263
  simp only [CollatzResearch.WordTrace]
  refine ⟨62451362195771057083869443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41634241463847371389246295 62451362195771057083869443)
  ·
    refine ⟨93677043293656585625804165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62451362195771057083869443 93677043293656585625804165)
    ·
      refine ⟨17564445617560609804838281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93677043293656585625804165 17564445617560609804838281)
      ·
        refine ⟨13173334213170457353628711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17564445617560609804838281 13173334213170457353628711)
        ·
          refine ⟨19760001319755686030443067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13173334213170457353628711 19760001319755686030443067)
          ·
            refine ⟨29640001979633529045664601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19760001319755686030443067 29640001979633529045664601)
            ·
              refine ⟨22230001484725146784248451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29640001979633529045664601 22230001484725146784248451)
              ·
                refine ⟨33345002227087720176372677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22230001484725146784248451 33345002227087720176372677)
                ·
                  refine ⟨6252187917578947533069877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33345002227087720176372677 6252187917578947533069877)
                  ·
                    refine ⟨586142617273026331225301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6252187917578947533069877 586142617273026331225301)
                    ·
                      rfl

theorem cell22_1712263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1712263 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712263 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712263 prefixEnd_1712263 := by exact prefixLift 1712263
  have htrace : WordTrace (prefixWord ++ tailWord_1712263) baseStart_1712263 baseEnd_1712263 := by
    simpa [prefixWord, tailWord_1712263, baseEnd_1712263] using wordTrace_append hprefix tailTrace_1712263
  have hstable : (prefixWord ++ tailWord_1712263).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712263).length < 2 ^ (prefixWord ++ tailWord_1712263).sum := by decide
  have hdescent : baseEnd_1712263 < baseStart_1712263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712282 : List Nat := [3, 1, 1, 5, 2, 1, 1, 3, 5]
def baseStart_1712282 : Nat := 118140960795 + 1712282 * 2 ^ 59
def prefixEnd_1712282 : Nat := 4983230072969 + 3 ^ 40 * 1712282 * 2
def baseEnd_1712282 : Nat := 195383040453772205000081

theorem tailTrace_1712282 : CollatzResearch.WordTrace tailWord_1712282 prefixEnd_1712282 195383040453772205000081 := by
  unfold tailWord_1712282
  simp only [CollatzResearch.WordTrace]
  refine ⟨15613013795675555832202775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41634703455134815552540733 15613013795675555832202775)
  ·
    refine ⟨23419520693513333748304163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15613013795675555832202775 23419520693513333748304163)
    ·
      refine ⟨35129281040270000622456245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23419520693513333748304163 35129281040270000622456245)
      ·
        refine ⟨3293370097525312558355273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35129281040270000622456245 3293370097525312558355273)
        ·
          refine ⟨2470027573143984418766455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3293370097525312558355273 2470027573143984418766455)
          ·
            refine ⟨3705041359715976628149683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2470027573143984418766455 3705041359715976628149683)
            ·
              refine ⟨5557562039573964942224525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3705041359715976628149683 5557562039573964942224525)
              ·
                refine ⟨2084085764840236853334197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5557562039573964942224525 2084085764840236853334197)
                ·
                  refine ⟨195383040453772205000081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2084085764840236853334197 195383040453772205000081)
                  ·
                    rfl

theorem cell22_1712282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 3, 5].length) (baseStart_1712282 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712282 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712282 prefixEnd_1712282 := by exact prefixLift 1712282
  have htrace : WordTrace (prefixWord ++ tailWord_1712282) baseStart_1712282 baseEnd_1712282 := by
    simpa [prefixWord, tailWord_1712282, baseEnd_1712282] using wordTrace_append hprefix tailTrace_1712282
  have hstable : (prefixWord ++ tailWord_1712282).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712282).length < 2 ^ (prefixWord ++ tailWord_1712282).sum := by decide
  have hdescent : baseEnd_1712282 < baseStart_1712282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712293 : List Nat := [1, 3, 1, 2, 1, 3, 2, 1, 8]
def baseStart_1712293 : Nat := 118140960795 + 1712293 * 2 ^ 59
def prefixEnd_1712293 : Nat := 4983230072969 + 3 ^ 40 * 1712293 * 2
def baseEnd_1712293 : Nat := 195384295628705417658403

theorem tailTrace_1712293 : CollatzResearch.WordTrace tailWord_1712293 prefixEnd_1712293 195384295628705417658403 := by
  unfold tailWord_1712293
  simp only [CollatzResearch.WordTrace]
  refine ⟨62452456385662372207461533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41634970923774914804974355 62452456385662372207461533)
  ·
    refine ⟨23419671144623389577798075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62452456385662372207461533 23419671144623389577798075)
    ·
      refine ⟨35129506716935084366697113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23419671144623389577798075 35129506716935084366697113)
      ·
        refine ⟨26347130037701313275022835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35129506716935084366697113 26347130037701313275022835)
        ·
          refine ⟨39520695056551969912534253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26347130037701313275022835 39520695056551969912534253)
          ·
            refine ⟨14820260646206988717200345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39520695056551969912534253 14820260646206988717200345)
            ·
              refine ⟨11115195484655241537900259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14820260646206988717200345 11115195484655241537900259)
              ·
                refine ⟨16672793226982862306850389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11115195484655241537900259 16672793226982862306850389)
                ·
                  refine ⟨195384295628705417658403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16672793226982862306850389 195384295628705417658403)
                  ·
                    rfl

theorem cell22_1712293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 1, 8].length) (baseStart_1712293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712293 prefixEnd_1712293 := by exact prefixLift 1712293
  have htrace : WordTrace (prefixWord ++ tailWord_1712293) baseStart_1712293 baseEnd_1712293 := by
    simpa [prefixWord, tailWord_1712293, baseEnd_1712293] using wordTrace_append hprefix tailTrace_1712293
  have hstable : (prefixWord ++ tailWord_1712293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712293).length < 2 ^ (prefixWord ++ tailWord_1712293).sum := by decide
  have hdescent : baseEnd_1712293 < baseStart_1712293 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712312 : List Nat := [2, 1, 2, 1, 2, 1, 7, 1, 1, 4]
def baseStart_1712312 : Nat := 118140960795 + 1712312 * 2 ^ 59
def prefixEnd_1712312 : Nat := 4983230072969 + 3 ^ 40 * 1712312 * 2
def baseEnd_1712312 : Nat := 586159390974406536750151

theorem tailTrace_1712312 : CollatzResearch.WordTrace tailWord_1712312 prefixEnd_1712312 586159390974406536750151 := by
  unfold tailWord_1712312
  simp only [CollatzResearch.WordTrace]
  refine ⟨31226574686296769226201595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41635432915062358968268793 31226574686296769226201595)
  ·
    refine ⟨46839862029445153839302393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31226574686296769226201595 46839862029445153839302393)
    ·
      refine ⟨35129896522083865379476795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46839862029445153839302393 35129896522083865379476795)
      ·
        refine ⟨52694844783125798069215193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35129896522083865379476795 52694844783125798069215193)
        ·
          refine ⟨39521133587344348551911395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52694844783125798069215193 39521133587344348551911395)
          ·
            refine ⟨59281700381016522827867093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39521133587344348551911395 59281700381016522827867093)
            ·
              refine ⟨1389414852680074753778135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 59281700381016522827867093 1389414852680074753778135)
              ·
                refine ⟨2084122279020112130667203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1389414852680074753778135 2084122279020112130667203)
                ·
                  refine ⟨3126183418530168196000805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084122279020112130667203 3126183418530168196000805)
                  ·
                    refine ⟨586159390974406536750151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3126183418530168196000805 586159390974406536750151)
                    ·
                      rfl

theorem cell22_1712312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 7, 1, 1, 4].length) (baseStart_1712312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712312 prefixEnd_1712312 := by exact prefixLift 1712312
  have htrace : WordTrace (prefixWord ++ tailWord_1712312) baseStart_1712312 baseEnd_1712312 := by
    simpa [prefixWord, tailWord_1712312, baseEnd_1712312] using wordTrace_append hprefix tailTrace_1712312
  have hstable : (prefixWord ++ tailWord_1712312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712312).length < 2 ^ (prefixWord ++ tailWord_1712312).sum := by decide
  have hdescent : baseEnd_1712312 < baseStart_1712312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712325 : List Nat := [1, 3, 1, 1, 1, 1, 4, 3, 4, 3]
def baseStart_1712325 : Nat := 118140960795 + 1712325 * 2 ^ 59
def prefixEnd_1712325 : Nat := 4983230072969 + 3 ^ 40 * 1712325 * 2
def baseEnd_1712325 : Nat := 586163841140078836175111

theorem tailTrace_1712325 : CollatzResearch.WordTrace tailWord_1712325 prefixEnd_1712325 586163841140078836175111 := by
  unfold tailWord_1712325
  simp only [CollatzResearch.WordTrace]
  refine ⟨62453623521546441672626429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41635749014364294448417619 62453623521546441672626429)
  ·
    refine ⟨23420108820579915627234911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62453623521546441672626429 23420108820579915627234911)
    ·
      refine ⟨35130163230869873440852367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23420108820579915627234911 35130163230869873440852367)
      ·
        refine ⟨52695244846304810161278551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35130163230869873440852367 52695244846304810161278551)
        ·
          refine ⟨79042867269457215241917827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52695244846304810161278551 79042867269457215241917827)
          ·
            refine ⟨118564300904185822862876741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79042867269457215241917827 118564300904185822862876741)
            ·
              refine ⟨22230806419534841786789389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118564300904185822862876741 22230806419534841786789389)
              ·
                refine ⟨8336552407325565670046021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22230806419534841786789389 8336552407325565670046021)
                ·
                  refine ⟨1563103576373543563133629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8336552407325565670046021 1563103576373543563133629)
                  ·
                    refine ⟨586163841140078836175111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1563103576373543563133629 586163841140078836175111)
                    ·
                      rfl

theorem cell22_1712325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 3].length) (baseStart_1712325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712325 prefixEnd_1712325 := by exact prefixLift 1712325
  have htrace : WordTrace (prefixWord ++ tailWord_1712325) baseStart_1712325 baseEnd_1712325 := by
    simpa [prefixWord, tailWord_1712325, baseEnd_1712325] using wordTrace_append hprefix tailTrace_1712325
  have hstable : (prefixWord ++ tailWord_1712325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712325).length < 2 ^ (prefixWord ++ tailWord_1712325).sum := by decide
  have hdescent : baseEnd_1712325 < baseStart_1712325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712357 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 2, 4]
def baseStart_1712357 : Nat := 118140960795 + 1712357 * 2 ^ 59
def prefixEnd_1712357 : Nat := 4983230072969 + 3 ^ 40 * 1712357 * 2
def baseEnd_1712357 : Nat := 586174795394041419375013

theorem tailTrace_1712357 : CollatzResearch.WordTrace tailWord_1712357 prefixEnd_1712357 586174795394041419375013 := by
  unfold tailWord_1712357
  simp only [CollatzResearch.WordTrace]
  refine ⟨62454790657430511137791325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41636527104953674091860883 62454790657430511137791325)
  ·
    refine ⟨23420546496536441676671747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62454790657430511137791325 23420546496536441676671747)
    ·
      refine ⟨35130819744804662515007621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23420546496536441676671747 35130819744804662515007621)
      ·
        refine ⟨6587028702150874221563929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35130819744804662515007621 6587028702150874221563929)
        ·
          refine ⟨4940271526613155666172947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6587028702150874221563929 4940271526613155666172947)
          ·
            refine ⟨7410407289919733499259421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4940271526613155666172947 7410407289919733499259421)
            ·
              refine ⟨2778902733719900062222283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7410407289919733499259421 2778902733719900062222283)
              ·
                refine ⟨4168354100579850093333425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778902733719900062222283 4168354100579850093333425)
                ·
                  refine ⟨3126265575434887570000069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4168354100579850093333425 3126265575434887570000069)
                  ·
                    refine ⟨586174795394041419375013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3126265575434887570000069 586174795394041419375013)
                    ·
                      rfl

theorem cell22_1712357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 2, 4].length) (baseStart_1712357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712357 prefixEnd_1712357 := by exact prefixLift 1712357
  have htrace : WordTrace (prefixWord ++ tailWord_1712357) baseStart_1712357 baseEnd_1712357 := by
    simpa [prefixWord, tailWord_1712357, baseEnd_1712357] using wordTrace_append hprefix tailTrace_1712357
  have hstable : (prefixWord ++ tailWord_1712357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712357).length < 2 ^ (prefixWord ++ tailWord_1712357).sum := by decide
  have hdescent : baseEnd_1712357 < baseStart_1712357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712387 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 3, 3]
def baseStart_1712387 : Nat := 118140960795 + 1712387 * 2 ^ 59
def prefixEnd_1712387 : Nat := 4983230072969 + 3 ^ 40 * 1712387 * 2
def baseEnd_1712387 : Nat := 586185065007131341124921

theorem tailTrace_1712387 : CollatzResearch.WordTrace tailWord_1712387 prefixEnd_1712387 586185065007131341124921 := by
  unfold tailWord_1712387
  simp only [CollatzResearch.WordTrace]
  refine ⟨62455884847321826261383415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41637256564881217507588943 62455884847321826261383415)
  ·
    refine ⟨93683827270982739392075123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62455884847321826261383415 93683827270982739392075123)
    ·
      refine ⟨140525740906474109088112685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93683827270982739392075123 140525740906474109088112685)
      ·
        refine ⟨52697152839927790908042257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140525740906474109088112685 52697152839927790908042257)
        ·
          refine ⟨39522864629945843181031693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52697152839927790908042257 39522864629945843181031693)
          ·
            refine ⟨14821074236229691192886885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39522864629945843181031693 14821074236229691192886885)
            ·
              refine ⟨2778951419293067098666291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14821074236229691192886885 2778951419293067098666291)
              ·
                refine ⟨4168427128939600647999437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2778951419293067098666291 4168427128939600647999437)
                ·
                  refine ⟨1563160173352350242999789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4168427128939600647999437 1563160173352350242999789)
                  ·
                    refine ⟨586185065007131341124921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1563160173352350242999789 586185065007131341124921)
                    ·
                      rfl

theorem cell22_1712387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 3, 3].length) (baseStart_1712387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712387 prefixEnd_1712387 := by exact prefixLift 1712387
  have htrace : WordTrace (prefixWord ++ tailWord_1712387) baseStart_1712387 baseEnd_1712387 := by
    simpa [prefixWord, tailWord_1712387, baseEnd_1712387] using wordTrace_append hprefix tailTrace_1712387
  have hstable : (prefixWord ++ tailWord_1712387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712387).length < 2 ^ (prefixWord ++ tailWord_1712387).sum := by decide
  have hdescent : baseEnd_1712387 < baseStart_1712387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712464 : List Nat := [2, 1, 1, 1, 1, 8, 1, 2, 1, 4]
def baseStart_1712464 : Nat := 118140960795 + 1712464 * 2 ^ 59
def prefixEnd_1712464 : Nat := 4983230072969 + 3 ^ 40 * 1712464 * 2
def baseEnd_1712464 : Nat := 586211423680728806949685

theorem tailTrace_1712464 : CollatzResearch.WordTrace tailWord_1712464 prefixEnd_1712464 586211423680728806949685 := by
  unfold tailWord_1712464
  simp only [CollatzResearch.WordTrace]
  refine ⟨31229346634021434205968223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41639128845361912274624297 31229346634021434205968223)
  ·
    refine ⟨46844019951032151308952335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31229346634021434205968223 46844019951032151308952335)
    ·
      refine ⟨70266029926548226963428503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46844019951032151308952335 70266029926548226963428503)
      ·
        refine ⟨105399044889822340445142755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70266029926548226963428503 105399044889822340445142755)
        ·
          refine ⟨158098567334733510667714133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105399044889822340445142755 158098567334733510667714133)
          ·
            refine ⟨1852717585953908328137275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 158098567334733510667714133 1852717585953908328137275)
            ·
              refine ⟨2779076378930862492205913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852717585953908328137275 2779076378930862492205913)
              ·
                refine ⟨2084307284198146869154435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779076378930862492205913 2084307284198146869154435)
                ·
                  refine ⟨3126460926297220303731653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2084307284198146869154435 3126460926297220303731653)
                  ·
                    refine ⟨586211423680728806949685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3126460926297220303731653 586211423680728806949685)
                    ·
                      rfl

theorem cell22_1712464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 8, 1, 2, 1, 4].length) (baseStart_1712464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712464 prefixEnd_1712464 := by exact prefixLift 1712464
  have htrace : WordTrace (prefixWord ++ tailWord_1712464) baseStart_1712464 baseEnd_1712464 := by
    simpa [prefixWord, tailWord_1712464, baseEnd_1712464] using wordTrace_append hprefix tailTrace_1712464
  have hstable : (prefixWord ++ tailWord_1712464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712464).length < 2 ^ (prefixWord ++ tailWord_1712464).sum := by decide
  have hdescent : baseEnd_1712464 < baseStart_1712464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712496 : List Nat := [2, 1, 1, 1, 4, 5, 2, 2, 4]
def baseStart_1712496 : Nat := 118140960795 + 1712496 * 2 ^ 59
def prefixEnd_1712496 : Nat := 4983230072969 + 3 ^ 40 * 1712496 * 2
def baseEnd_1712496 : Nat := 195407459311563796716529

theorem tailTrace_1712496 : CollatzResearch.WordTrace tailWord_1712496 prefixEnd_1712496 195407459311563796716529 := by
  unfold tailWord_1712496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31229930201963468938550671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41639906935951291918067561 31229930201963468938550671)
  ·
    refine ⟨46844895302945203407826007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31229930201963468938550671 46844895302945203407826007)
    ·
      refine ⟨70267342954417805111739011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46844895302945203407826007 70267342954417805111739011)
      ·
        refine ⟨105401014431626707667608517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70267342954417805111739011 105401014431626707667608517)
        ·
          refine ⟨19762690205930007687676597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105401014431626707667608517 19762690205930007687676597)
          ·
            refine ⟨1852752206805938220719681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19762690205930007687676597 1852752206805938220719681)
            ·
              refine ⟨1389564155104453665539761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1852752206805938220719681 1389564155104453665539761)
              ·
                refine ⟨1042173116328340249154821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1389564155104453665539761 1042173116328340249154821)
                ·
                  refine ⟨195407459311563796716529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1042173116328340249154821 195407459311563796716529)
                  ·
                    rfl

theorem cell22_1712496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 2, 2, 4].length) (baseStart_1712496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712496 prefixEnd_1712496 := by exact prefixLift 1712496
  have htrace : WordTrace (prefixWord ++ tailWord_1712496) baseStart_1712496 baseEnd_1712496 := by
    simpa [prefixWord, tailWord_1712496, baseEnd_1712496] using wordTrace_append hprefix tailTrace_1712496
  have hstable : (prefixWord ++ tailWord_1712496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712496).length < 2 ^ (prefixWord ++ tailWord_1712496).sum := by decide
  have hdescent : baseEnd_1712496 < baseStart_1712496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712505 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 2, 7]
def baseStart_1712505 : Nat := 118140960795 + 1712505 * 2 ^ 59
def prefixEnd_1712505 : Nat := 4983230072969 + 3 ^ 40 * 1712505 * 2
def baseEnd_1712505 : Nat := 586225458818618366674559

theorem tailTrace_1712505 : CollatzResearch.WordTrace tailWord_1712505 prefixEnd_1712505 586225458818618366674559 := by
  unfold tailWord_1712505
  simp only [CollatzResearch.WordTrace]
  refine ⟨62460188660894332414178969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41640125773929554942785979 62460188660894332414178969)
  ·
    refine ⟨46845141495670749310634227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62460188660894332414178969 46845141495670749310634227)
    ·
      refine ⟨70267712243506123965951341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46845141495670749310634227 70267712243506123965951341)
      ·
        refine ⟨26350392091314796487231753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70267712243506123965951341 26350392091314796487231753)
        ·
          refine ⟨19762794068486097365423815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26350392091314796487231753 19762794068486097365423815)
          ·
            refine ⟨29644191102729146048135723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19762794068486097365423815 29644191102729146048135723)
            ·
              refine ⟨44466286654093719072203585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29644191102729146048135723 44466286654093719072203585)
              ·
                refine ⟨33349714990570289304152689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44466286654093719072203585 33349714990570289304152689)
                ·
                  refine ⟨25012286242927716978114517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33349714990570289304152689 25012286242927716978114517)
                  ·
                    refine ⟨586225458818618366674559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25012286242927716978114517 586225458818618366674559)
                    ·
                      rfl

theorem cell22_1712505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 7].length) (baseStart_1712505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712505 prefixEnd_1712505 := by exact prefixLift 1712505
  have htrace : WordTrace (prefixWord ++ tailWord_1712505) baseStart_1712505 baseEnd_1712505 := by
    simpa [prefixWord, tailWord_1712505, baseEnd_1712505] using wordTrace_append hprefix tailTrace_1712505
  have hstable : (prefixWord ++ tailWord_1712505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712505).length < 2 ^ (prefixWord ++ tailWord_1712505).sum := by decide
  have hdescent : baseEnd_1712505 < baseStart_1712505 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712507 : List Nat := [1, 1, 1, 1, 1, 9, 1, 7]
def baseStart_1712507 : Nat := 118140960795 + 1712507 * 2 ^ 59
def prefixEnd_1712507 : Nat := 4983230072969 + 3 ^ 40 * 1712507 * 2
def baseEnd_1712507 : Nat := 65136238162165669791617

theorem tailTrace_1712507 : CollatzResearch.WordTrace tailWord_1712507 prefixEnd_1712507 65136238162165669791617 := by
  unfold tailWord_1712507
  simp only [CollatzResearch.WordTrace]
  refine ⟨62460261606887086755751775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41640174404591391170501183 62460261606887086755751775)
  ·
    refine ⟨93690392410330630133627663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62460261606887086755751775 93690392410330630133627663)
    ·
      refine ⟨140535588615495945200441495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93690392410330630133627663 140535588615495945200441495)
      ·
        refine ⟨210803382923243917800662243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140535588615495945200441495 210803382923243917800662243)
        ·
          refine ⟨316205074384865876700993365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210803382923243917800662243 316205074384865876700993365)
          ·
            refine ⟨1852764107723823496294883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 316205074384865876700993365 1852764107723823496294883)
            ·
              refine ⟨2779146161585735244442325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852764107723823496294883 2779146161585735244442325)
              ·
                refine ⟨65136238162165669791617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2779146161585735244442325 65136238162165669791617)
                ·
                  rfl

theorem cell22_1712507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 1, 7].length) (baseStart_1712507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712507 prefixEnd_1712507 := by exact prefixLift 1712507
  have htrace : WordTrace (prefixWord ++ tailWord_1712507) baseStart_1712507 baseEnd_1712507 := by
    simpa [prefixWord, tailWord_1712507, baseEnd_1712507] using wordTrace_append hprefix tailTrace_1712507
  have hstable : (prefixWord ++ tailWord_1712507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712507).length < 2 ^ (prefixWord ++ tailWord_1712507).sum := by decide
  have hdescent : baseEnd_1712507 < baseStart_1712507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712526 : List Nat := [4, 1, 1, 4, 1, 3, 1, 1, 2, 4]
def baseStart_1712526 : Nat := 118140960795 + 1712526 * 2 ^ 59
def prefixEnd_1712526 : Nat := 4983230072969 + 3 ^ 40 * 1712526 * 2
def baseEnd_1712526 : Nat := 586232647547781311899495

theorem tailTrace_1712526 : CollatzResearch.WordTrace tailWord_1712526 prefixEnd_1712526 586232647547781311899495 := by
  unfold tailWord_1712526
  simp only [CollatzResearch.WordTrace]
  refine ⟨7807619324227281625086679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41640636395878835333795621 7807619324227281625086679)
  ·
    refine ⟨11711428986340922437630019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7807619324227281625086679 11711428986340922437630019)
    ·
      refine ⟨17567143479511383656445029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11711428986340922437630019 17567143479511383656445029)
      ·
        refine ⟨3293839402408384435583443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17567143479511383656445029 3293839402408384435583443)
        ·
          refine ⟨4940759103612576653375165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3293839402408384435583443 4940759103612576653375165)
          ·
            refine ⟨1852784663854716245015687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4940759103612576653375165 1852784663854716245015687)
            ·
              refine ⟨2779176995782074367523531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852784663854716245015687 2779176995782074367523531)
              ·
                refine ⟨4168765493673111551285297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779176995782074367523531 4168765493673111551285297)
                ·
                  refine ⟨3126574120254833663463973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4168765493673111551285297 3126574120254833663463973)
                  ·
                    refine ⟨586232647547781311899495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3126574120254833663463973 586232647547781311899495)
                    ·
                      rfl

theorem cell22_1712526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_1712526 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712526 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712526 prefixEnd_1712526 := by exact prefixLift 1712526
  have htrace : WordTrace (prefixWord ++ tailWord_1712526) baseStart_1712526 baseEnd_1712526 := by
    simpa [prefixWord, tailWord_1712526, baseEnd_1712526] using wordTrace_append hprefix tailTrace_1712526
  have hstable : (prefixWord ++ tailWord_1712526).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712526).length < 2 ^ (prefixWord ++ tailWord_1712526).sum := by decide
  have hdescent : baseEnd_1712526 < baseStart_1712526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712545 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 2, 3]
def baseStart_1712545 : Nat := 118140960795 + 1712545 * 2 ^ 59
def prefixEnd_1712545 : Nat := 4983230072969 + 3 ^ 40 * 1712545 * 2
def baseEnd_1712545 : Nat := 586239151636071595674437

theorem tailTrace_1712545 : CollatzResearch.WordTrace tailWord_1712545 prefixEnd_1712545 586239151636071595674437 := by
  unfold tailWord_1712545
  simp only [CollatzResearch.WordTrace]
  refine ⟨62461647580749419245635089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41641098387166279497090059 62461647580749419245635089)
  ·
    refine ⟨46846235685562064434226317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62461647580749419245635089 46846235685562064434226317)
    ·
      refine ⟨17567338382085774162834869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46846235685562064434226317 17567338382085774162834869)
      ·
        refine ⟨1646937973320541327765769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17567338382085774162834869 1646937973320541327765769)
        ·
          refine ⟨1235203479990405995824327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1646937973320541327765769 1235203479990405995824327)
          ·
            refine ⟨1852805219985608993736491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235203479990405995824327 1852805219985608993736491)
            ·
              refine ⟨2779207829978413490604737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852805219985608993736491 2779207829978413490604737)
              ·
                refine ⟨2084405872483810117953553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779207829978413490604737 2084405872483810117953553)
                ·
                  refine ⟨1563304404362857588465165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2084405872483810117953553 1563304404362857588465165)
                  ·
                    refine ⟨586239151636071595674437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1563304404362857588465165 586239151636071595674437)
                    ·
                      rfl

theorem cell22_1712545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 2, 3].length) (baseStart_1712545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712545 prefixEnd_1712545 := by exact prefixLift 1712545
  have htrace : WordTrace (prefixWord ++ tailWord_1712545) baseStart_1712545 baseEnd_1712545 := by
    simpa [prefixWord, tailWord_1712545, baseEnd_1712545] using wordTrace_append hprefix tailTrace_1712545
  have hstable : (prefixWord ++ tailWord_1712545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712545).length < 2 ^ (prefixWord ++ tailWord_1712545).sum := by decide
  have hdescent : baseEnd_1712545 < baseStart_1712545 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712567 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 2, 5]
def baseStart_1712567 : Nat := 118140960795 + 1712567 * 2 ^ 59
def prefixEnd_1712567 : Nat := 4983230072969 + 3 ^ 40 * 1712567 * 2
def baseEnd_1712567 : Nat := 586246682685670871624369

theorem tailTrace_1712567 : CollatzResearch.WordTrace tailWord_1712567 prefixEnd_1712567 586246682685670871624369 := by
  unfold tailWord_1712567
  simp only [CollatzResearch.WordTrace]
  refine ⟨62462449986669717002935955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41641633324446478001957303 62462449986669717002935955)
  ·
    refine ⟨93693674980004575504403933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62462449986669717002935955 93693674980004575504403933)
    ·
      refine ⟨35135128117501715814151475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93693674980004575504403933 35135128117501715814151475)
      ·
        refine ⟨52702692176252573721227213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35135128117501715814151475 52702692176252573721227213)
        ·
          refine ⟨19763509566094715145460205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52702692176252573721227213 19763509566094715145460205)
          ·
            refine ⟨7411316087285518179547577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19763509566094715145460205 7411316087285518179547577)
            ·
              refine ⟨5558487065464138634660683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7411316087285518179547577 5558487065464138634660683)
              ·
                refine ⟨8337730598196207951991025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5558487065464138634660683 8337730598196207951991025)
                ·
                  refine ⟨6253297948647155963993269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8337730598196207951991025 6253297948647155963993269)
                  ·
                    refine ⟨586246682685670871624369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6253297948647155963993269 586246682685670871624369)
                    ·
                      rfl

theorem cell22_1712567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 2, 5].length) (baseStart_1712567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712567 prefixEnd_1712567 := by exact prefixLift 1712567
  have htrace : WordTrace (prefixWord ++ tailWord_1712567) baseStart_1712567 baseEnd_1712567 := by
    simpa [prefixWord, tailWord_1712567, baseEnd_1712567] using wordTrace_append hprefix tailTrace_1712567
  have hstable : (prefixWord ++ tailWord_1712567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712567).length < 2 ^ (prefixWord ++ tailWord_1712567).sum := by decide
  have hdescent : baseEnd_1712567 < baseStart_1712567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712627 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 4, 4]
def baseStart_1712627 : Nat := 118140960795 + 1712627 * 2 ^ 59
def prefixEnd_1712627 : Nat := 4983230072969 + 3 ^ 40 * 1712627 * 2
def baseEnd_1712627 : Nat := 586267221911850715124185

theorem tailTrace_1712627 : CollatzResearch.WordTrace tailWord_1712627 prefixEnd_1712627 586267221911850715124185 := by
  unfold tailWord_1712627
  simp only [CollatzResearch.WordTrace]
  refine ⟨62464638366452347250120135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41643092244301564833413423 62464638366452347250120135)
  ·
    refine ⟨93696957549678520875180203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62464638366452347250120135 93696957549678520875180203)
    ·
      refine ⟨140545436324517781312770305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93696957549678520875180203 140545436324517781312770305)
      ·
        refine ⟨105409077243388335984577729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140545436324517781312770305 105409077243388335984577729)
        ·
          refine ⟨79056807932541251988433297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105409077243388335984577729 79056807932541251988433297)
          ·
            refine ⟨59292605949405938991324973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79056807932541251988433297 59292605949405938991324973)
            ·
              refine ⟨22234727231027227121746865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59292605949405938991324973 22234727231027227121746865)
              ·
                refine ⟨16676045423270420341310149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22234727231027227121746865 16676045423270420341310149)
                ·
                  refine ⟨3126758516863203813995653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16676045423270420341310149 3126758516863203813995653)
                  ·
                    refine ⟨586267221911850715124185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3126758516863203813995653 586267221911850715124185)
                    ·
                      rfl

theorem cell22_1712627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 4, 4].length) (baseStart_1712627 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712627 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712627 prefixEnd_1712627 := by exact prefixLift 1712627
  have htrace : WordTrace (prefixWord ++ tailWord_1712627) baseStart_1712627 baseEnd_1712627 := by
    simpa [prefixWord, tailWord_1712627, baseEnd_1712627] using wordTrace_append hprefix tailTrace_1712627
  have hstable : (prefixWord ++ tailWord_1712627).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712627).length < 2 ^ (prefixWord ++ tailWord_1712627).sum := by decide
  have hdescent : baseEnd_1712627 < baseStart_1712627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712721 : List Nat := [1, 2, 2, 1, 3, 5, 1, 2, 5]
def baseStart_1712721 : Nat := 118140960795 + 1712721 * 2 ^ 59
def prefixEnd_1712721 : Nat := 4983230072969 + 3 ^ 40 * 1712721 * 2
def baseEnd_1712721 : Nat := 195433133344288601091299

theorem tailTrace_1712721 : CollatzResearch.WordTrace tailWord_1712721 prefixEnd_1712721 195433133344288601091299 := by
  unfold tailWord_1712721
  simp only [CollatzResearch.WordTrace]
  refine ⟨62468066828111801304042017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41645377885407867536028011 62468066828111801304042017)
  ·
    refine ⟨46851050121083850978031513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62468066828111801304042017 46851050121083850978031513)
    ·
      refine ⟨35138287590812888233523635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46851050121083850978031513 35138287590812888233523635)
      ·
        refine ⟨52707431386219332350285453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35138287590812888233523635 52707431386219332350285453)
        ·
          refine ⟨19765286769832249631357045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52707431386219332350285453 19765286769832249631357045)
          ·
            refine ⟨1852995634671773402939723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19765286769832249631357045 1852995634671773402939723)
            ·
              refine ⟨2779493452007660104409585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1852995634671773402939723 2779493452007660104409585)
              ·
                refine ⟨2084620089005745078307189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2779493452007660104409585 2084620089005745078307189)
                ·
                  refine ⟨195433133344288601091299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2084620089005745078307189 195433133344288601091299)
                  ·
                    rfl

theorem cell22_1712721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 1, 2, 5].length) (baseStart_1712721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712721 prefixEnd_1712721 := by exact prefixLift 1712721
  have htrace : WordTrace (prefixWord ++ tailWord_1712721) baseStart_1712721 baseEnd_1712721 := by
    simpa [prefixWord, tailWord_1712721, baseEnd_1712721] using wordTrace_append hprefix tailTrace_1712721
  have hstable : (prefixWord ++ tailWord_1712721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712721).length < 2 ^ (prefixWord ++ tailWord_1712721).sum := by decide
  have hdescent : baseEnd_1712721 < baseStart_1712721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712764 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 1, 5]
def baseStart_1712764 : Nat := 118140960795 + 1712764 * 2 ^ 59
def prefixEnd_1712764 : Nat := 4983230072969 + 3 ^ 40 * 1712764 * 2
def baseEnd_1712764 : Nat := 586314119811628024448765

theorem tailTrace_1712764 : CollatzResearch.WordTrace tailWord_1712764 prefixEnd_1712764 586314119811628024448765 := by
  unfold tailWord_1712764
  simp only [CollatzResearch.WordTrace]
  refine ⟨31234817583478009823928673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41646423444637346431904897 31234817583478009823928673)
  ·
    refine ⟨23426113187608507367946505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31234817583478009823928673 23426113187608507367946505)
    ·
      refine ⟨17569584890706380525959879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23426113187608507367946505 17569584890706380525959879)
      ·
        refine ⟨26354377336059570788939819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17569584890706380525959879 26354377336059570788939819)
        ·
          refine ⟨39531566004089356183409729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26354377336059570788939819 39531566004089356183409729)
          ·
            refine ⟨29648674503067017137557297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39531566004089356183409729 29648674503067017137557297)
            ·
              refine ⟨22236505877300262853167973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29648674503067017137557297 22236505877300262853167973)
              ·
                refine ⟨4169344851993799284968995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22236505877300262853167973 4169344851993799284968995)
                ·
                  refine ⟨6254017277990698927453493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4169344851993799284968995 6254017277990698927453493)
                  ·
                    refine ⟨586314119811628024448765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6254017277990698927453493 586314119811628024448765)
                    ·
                      rfl

theorem cell22_1712764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_1712764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712764 prefixEnd_1712764 := by exact prefixLift 1712764
  have htrace : WordTrace (prefixWord ++ tailWord_1712764) baseStart_1712764 baseEnd_1712764 := by
    simpa [prefixWord, tailWord_1712764, baseEnd_1712764] using wordTrace_append hprefix tailTrace_1712764
  have hstable : (prefixWord ++ tailWord_1712764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712764).length < 2 ^ (prefixWord ++ tailWord_1712764).sum := by decide
  have hdescent : baseEnd_1712764 < baseStart_1712764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712813 : List Nat := [1, 5, 2, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1712813 : Nat := 118140960795 + 1712813 * 2 ^ 59
def prefixEnd_1712813 : Nat := 4983230072969 + 3 ^ 40 * 1712813 * 2
def baseEnd_1712813 : Nat := 586330893513008229973615

theorem tailTrace_1712813 : CollatzResearch.WordTrace tailWord_1712813 prefixEnd_1712813 586330893513008229973615 := by
  unfold tailWord_1712813
  simp only [CollatzResearch.WordTrace]
  refine ⟨62471422343778501016391093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41647614895852334010927395 62471422343778501016391093)
  ·
    refine ⟨5856695844729234470286665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62471422343778501016391093 5856695844729234470286665)
    ·
      refine ⟨4392521883546925852714999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5856695844729234470286665 4392521883546925852714999)
      ·
        refine ⟨6588782825320388779072499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4392521883546925852714999 6588782825320388779072499)
        ·
          refine ⟨9883174237980583168608749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6588782825320388779072499 9883174237980583168608749)
          ·
            refine ⟨3706190339242718688228281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9883174237980583168608749 3706190339242718688228281)
            ·
              refine ⟨2779642754432039016171211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3706190339242718688228281 2779642754432039016171211)
              ·
                refine ⟨4169464131648058524256817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2779642754432039016171211 4169464131648058524256817)
                ·
                  refine ⟨3127098098736043893192613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4169464131648058524256817 3127098098736043893192613)
                  ·
                    refine ⟨586330893513008229973615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3127098098736043893192613 586330893513008229973615)
                    ·
                      rfl

theorem cell22_1712813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1712813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712813 prefixEnd_1712813 := by exact prefixLift 1712813
  have htrace : WordTrace (prefixWord ++ tailWord_1712813) baseStart_1712813 baseEnd_1712813 := by
    simpa [prefixWord, tailWord_1712813, baseEnd_1712813] using wordTrace_append hprefix tailTrace_1712813
  have hstable : (prefixWord ++ tailWord_1712813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712813).length < 2 ^ (prefixWord ++ tailWord_1712813).sum := by decide
  have hdescent : baseEnd_1712813 < baseStart_1712813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712845 : List Nat := [1, 6, 2, 1, 2, 2, 1, 7]
def baseStart_1712845 : Nat := 118140960795 + 1712845 * 2 ^ 59
def prefixEnd_1712845 : Nat := 4983230072969 + 3 ^ 40 * 1712845 * 2
def baseEnd_1712845 : Nat := 65149094196330090352613

theorem tailTrace_1712845 : CollatzResearch.WordTrace tailWord_1712845 prefixEnd_1712845 65149094196330090352613 := by
  unfold tailWord_1712845
  simp only [CollatzResearch.WordTrace]
  refine ⟨62472589479662570481555989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41648392986441713654370659 62472589479662570481555989)
  ·
    refine ⟨2928402631859182991322937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 62472589479662570481555989 2928402631859182991322937)
    ·
      refine ⟨2196301973894387243492203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2928402631859182991322937 2196301973894387243492203)
      ·
        refine ⟨3294452960841580865238305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2196301973894387243492203 3294452960841580865238305)
        ·
          refine ⟨2470839720631185648928729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3294452960841580865238305 2470839720631185648928729)
          ·
            refine ⟨1853129790473389236696547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2470839720631185648928729 1853129790473389236696547)
            ·
              refine ⟨2779694685710083855044821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853129790473389236696547 2779694685710083855044821)
              ·
                refine ⟨65149094196330090352613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2779694685710083855044821 65149094196330090352613)
                ·
                  rfl

theorem cell22_1712845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 1, 7].length) (baseStart_1712845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712845 prefixEnd_1712845 := by exact prefixLift 1712845
  have htrace : WordTrace (prefixWord ++ tailWord_1712845) baseStart_1712845 baseEnd_1712845 := by
    simpa [prefixWord, tailWord_1712845, baseEnd_1712845] using wordTrace_append hprefix tailTrace_1712845
  have hstable : (prefixWord ++ tailWord_1712845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712845).length < 2 ^ (prefixWord ++ tailWord_1712845).sum := by decide
  have hdescent : baseEnd_1712845 < baseStart_1712845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712856 : List Nat := [2, 1, 2, 2, 3, 2, 2, 3, 5]
def baseStart_1712856 : Nat := 118140960795 + 1712856 * 2 ^ 59
def prefixEnd_1712856 : Nat := 4983230072969 + 3 ^ 40 * 1712856 * 2
def baseEnd_1712856 : Nat := 195448537763923483716161

theorem tailTrace_1712856 : CollatzResearch.WordTrace tailWord_1712856 prefixEnd_1712856 195448537763923483716161 := by
  unfold tailWord_1712856
  simp only [CollatzResearch.WordTrace]
  refine ⟨31236495341311359680103211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41648660455081812906804281 31236495341311359680103211)
  ·
    refine ⟨46854743011967039520154817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31236495341311359680103211 46854743011967039520154817)
    ·
      refine ⟨35141057258975279640116113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46854743011967039520154817 35141057258975279640116113)
      ·
        refine ⟨26355792944231459730087085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35141057258975279640116113 26355792944231459730087085)
        ·
          refine ⟨9883422354086797398782657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26355792944231459730087085 9883422354086797398782657)
          ·
            refine ⟨7412566765565098049086993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9883422354086797398782657 7412566765565098049086993)
            ·
              refine ⟨5559425074173823536815245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7412566765565098049086993 5559425074173823536815245)
              ·
                refine ⟨2084784402815183826305717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5559425074173823536815245 2084784402815183826305717)
                ·
                  refine ⟨195448537763923483716161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2084784402815183826305717 195448537763923483716161)
                  ·
                    rfl

theorem cell22_1712856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 3, 5].length) (baseStart_1712856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712856 prefixEnd_1712856 := by exact prefixLift 1712856
  have htrace : WordTrace (prefixWord ++ tailWord_1712856) baseStart_1712856 baseEnd_1712856 := by
    simpa [prefixWord, tailWord_1712856, baseEnd_1712856] using wordTrace_append hprefix tailTrace_1712856
  have hstable : (prefixWord ++ tailWord_1712856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712856).length < 2 ^ (prefixWord ++ tailWord_1712856).sum := by decide
  have hdescent : baseEnd_1712856 < baseStart_1712856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712860 : List Nat := [2, 2, 5, 1, 1, 2, 1, 2, 3, 3]
def baseStart_1712860 : Nat := 118140960795 + 1712860 * 2 ^ 59
def prefixEnd_1712860 : Nat := 4983230072969 + 3 ^ 40 * 1712860 * 2
def baseEnd_1712860 : Nat := 586346982573515774048471

theorem tailTrace_1712860 : CollatzResearch.WordTrace tailWord_1712860 prefixEnd_1712860 586346982573515774048471 := by
  unfold tailWord_1712860
  simp only [CollatzResearch.WordTrace]
  refine ⟨31236568287304114021676017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41648757716405485362234689 31236568287304114021676017)
  ·
    refine ⟨23427426215478085516257013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31236568287304114021676017 23427426215478085516257013)
    ·
      refine ⟨2196321207701070517149095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23427426215478085516257013 2196321207701070517149095)
      ·
        refine ⟨3294481811551605775723643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2196321207701070517149095 3294481811551605775723643)
        ·
          refine ⟨4941722717327408663585465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3294481811551605775723643 4941722717327408663585465)
          ·
            refine ⟨3706292037995556497689099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4941722717327408663585465 3706292037995556497689099)
            ·
              refine ⟨5559438056993334746533649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3706292037995556497689099 5559438056993334746533649)
              ·
                refine ⟨4169578542745001059900237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5559438056993334746533649 4169578542745001059900237)
                ·
                  refine ⟨1563591953529375397462589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4169578542745001059900237 1563591953529375397462589)
                  ·
                    refine ⟨586346982573515774048471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1563591953529375397462589 586346982573515774048471)
                    ·
                      rfl

theorem cell22_1712860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_1712860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712860 prefixEnd_1712860 := by exact prefixLift 1712860
  have htrace : WordTrace (prefixWord ++ tailWord_1712860) baseStart_1712860 baseEnd_1712860 := by
    simpa [prefixWord, tailWord_1712860, baseEnd_1712860] using wordTrace_append hprefix tailTrace_1712860
  have hstable : (prefixWord ++ tailWord_1712860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712860).length < 2 ^ (prefixWord ++ tailWord_1712860).sum := by decide
  have hdescent : baseEnd_1712860 < baseStart_1712860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712931 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 2, 4]
def baseStart_1712931 : Nat := 118140960795 + 1712931 * 2 ^ 59
def prefixEnd_1712931 : Nat := 4983230072969 + 3 ^ 40 * 1712931 * 2
def baseEnd_1712931 : Nat := 586371287324495255523253

theorem tailTrace_1712931 : CollatzResearch.WordTrace tailWord_1712931 prefixEnd_1712931 586371287324495255523253 := by
  unfold tailWord_1712931
  simp only [CollatzResearch.WordTrace]
  refine ⟨62475726157351007169186647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41650484104900671446124431 62475726157351007169186647)
  ·
    refine ⟨93713589236026510753779971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62475726157351007169186647 93713589236026510753779971)
    ·
      refine ⟨140570383854039766130669957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93713589236026510753779971 140570383854039766130669957)
      ·
        refine ⟨26356946972632456149500617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140570383854039766130669957 26356946972632456149500617)
        ·
          refine ⟨19767710229474342112125463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26356946972632456149500617 19767710229474342112125463)
          ·
            refine ⟨29651565344211513168188195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19767710229474342112125463 29651565344211513168188195)
            ·
              refine ⟨44477348016317269752282293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29651565344211513168188195 44477348016317269752282293)
              ·
                refine ⟨4169751376529744039276465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44477348016317269752282293 4169751376529744039276465)
                ·
                  refine ⟨3127313532397308029457349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4169751376529744039276465 3127313532397308029457349)
                  ·
                    refine ⟨586371287324495255523253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3127313532397308029457349 586371287324495255523253)
                    ·
                      rfl

theorem cell22_1712931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 2, 4].length) (baseStart_1712931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712931 prefixEnd_1712931 := by exact prefixLift 1712931
  have htrace : WordTrace (prefixWord ++ tailWord_1712931) baseStart_1712931 baseEnd_1712931 := by
    simpa [prefixWord, tailWord_1712931, baseEnd_1712931] using wordTrace_append hprefix tailTrace_1712931
  have hstable : (prefixWord ++ tailWord_1712931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712931).length < 2 ^ (prefixWord ++ tailWord_1712931).sum := by decide
  have hdescent : baseEnd_1712931 < baseStart_1712931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1712978 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_1712978 : Nat := 118140960795 + 1712978 * 2 ^ 59
def prefixEnd_1712978 : Nat := 4983230072969 + 3 ^ 40 * 1712978 * 2
def baseEnd_1712978 : Nat := 586387376385002799598109

theorem tailTrace_1712978 : CollatzResearch.WordTrace tailWord_1712978 prefixEnd_1712978 586387376385002799598109 := by
  unfold tailWord_1712978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15619360097045183549036897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41651626925453822797431725 15619360097045183549036897)
  ·
    refine ⟨11714520072783887661777673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15619360097045183549036897 11714520072783887661777673)
    ·
      refine ⟨8785890054587915746333255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11714520072783887661777673 8785890054587915746333255)
      ·
        refine ⟨13178835081881873619499883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8785890054587915746333255 13178835081881873619499883)
        ·
          refine ⟨19768252622822810429249825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13178835081881873619499883 19768252622822810429249825)
          ·
            refine ⟨14826189467117107821937369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19768252622822810429249825 14826189467117107821937369)
            ·
              refine ⟨11119642100337830866453027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14826189467117107821937369 11119642100337830866453027)
              ·
                refine ⟨16679463150506746299679541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11119642100337830866453027 16679463150506746299679541)
                ·
                  refine ⟨1563699670360007465594957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16679463150506746299679541 1563699670360007465594957)
                  ·
                    refine ⟨586387376385002799598109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1563699670360007465594957 586387376385002799598109)
                    ·
                      rfl

theorem cell22_1712978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_1712978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1712978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1712978 prefixEnd_1712978 := by exact prefixLift 1712978
  have htrace : WordTrace (prefixWord ++ tailWord_1712978) baseStart_1712978 baseEnd_1712978 := by
    simpa [prefixWord, tailWord_1712978, baseEnd_1712978] using wordTrace_append hprefix tailTrace_1712978
  have hstable : (prefixWord ++ tailWord_1712978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1712978).length < 2 ^ (prefixWord ++ tailWord_1712978).sum := by decide
  have hdescent : baseEnd_1712978 < baseStart_1712978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1712978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713036 : List Nat := [2, 2, 1, 2, 1, 2, 3, 1, 8]
def baseStart_1713036 : Nat := 118140960795 + 1713036 * 2 ^ 59
def prefixEnd_1713036 : Nat := 4983230072969 + 3 ^ 40 * 1713036 * 2
def baseEnd_1713036 : Nat := 195469076990103327215977

theorem tailTrace_1713036 : CollatzResearch.WordTrace tailWord_1713036 prefixEnd_1713036 195469076990103327215977 := by
  unfold tailWord_1713036
  simp only [CollatzResearch.WordTrace]
  refine ⟨31239777910985305050879481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41653037214647073401172641 31239777910985305050879481)
  ·
    refine ⟨23429833433238978788159611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31239777910985305050879481 23429833433238978788159611)
    ·
      refine ⟨35144750149858468182239417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23429833433238978788159611 35144750149858468182239417)
      ·
        refine ⟨26358562612393851136679563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35144750149858468182239417 26358562612393851136679563)
        ·
          refine ⟨39537843918590776705019345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26358562612393851136679563 39537843918590776705019345)
          ·
            refine ⟨29653382938943082528764509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39537843918590776705019345 29653382938943082528764509)
            ·
              refine ⟨11120018602103655948286691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29653382938943082528764509 11120018602103655948286691)
              ·
                refine ⟨16680027903155483922430037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11120018602103655948286691 16680027903155483922430037)
                ·
                  refine ⟨195469076990103327215977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16680027903155483922430037 195469076990103327215977)
                  ·
                    rfl

theorem cell22_1713036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 1, 8].length) (baseStart_1713036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713036 prefixEnd_1713036 := by exact prefixLift 1713036
  have htrace : WordTrace (prefixWord ++ tailWord_1713036) baseStart_1713036 baseEnd_1713036 := by
    simpa [prefixWord, tailWord_1713036, baseEnd_1713036] using wordTrace_append hprefix tailTrace_1713036
  have hstable : (prefixWord ++ tailWord_1713036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713036).length < 2 ^ (prefixWord ++ tailWord_1713036).sum := by decide
  have hdescent : baseEnd_1713036 < baseStart_1713036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713046 : List Nat := [5, 3, 1, 1, 1, 1, 1, 5, 1, 3]
def baseStart_1713046 : Nat := 118140960795 + 1713046 * 2 ^ 59
def prefixEnd_1713046 : Nat := 4983230072969 + 3 ^ 40 * 1713046 * 2
def baseEnd_1713046 : Nat := 586410654174673288897901

theorem tailTrace_1713046 : CollatzResearch.WordTrace tailWord_1713046 prefixEnd_1713046 586410654174673288897901 := by
  unfold tailWord_1713046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3904995034495898863101437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41653280367956254539748661 3904995034495898863101437)
  ·
    refine ⟨1464373137935962073663039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3904995034495898863101437 1464373137935962073663039)
    ·
      refine ⟨2196559706903943110494559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1464373137935962073663039 2196559706903943110494559)
      ·
        refine ⟨3294839560355914665741839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2196559706903943110494559 3294839560355914665741839)
        ·
          refine ⟨4942259340533871998612759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3294839560355914665741839 4942259340533871998612759)
          ·
            refine ⟨7413389010800807997919139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4942259340533871998612759 7413389010800807997919139)
            ·
              refine ⟨11120083516201211996878709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7413389010800807997919139 11120083516201211996878709)
              ·
                refine ⟨1042507829643863624707379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11120083516201211996878709 1042507829643863624707379)
                ·
                  refine ⟨1563761744465795437061069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042507829643863624707379 1563761744465795437061069)
                  ·
                    refine ⟨586410654174673288897901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1563761744465795437061069 586410654174673288897901)
                    ·
                      rfl

theorem cell22_1713046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_1713046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713046 prefixEnd_1713046 := by exact prefixLift 1713046
  have htrace : WordTrace (prefixWord ++ tailWord_1713046) baseStart_1713046 baseEnd_1713046 := by
    simpa [prefixWord, tailWord_1713046, baseEnd_1713046] using wordTrace_append hprefix tailTrace_1713046
  have hstable : (prefixWord ++ tailWord_1713046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713046).length < 2 ^ (prefixWord ++ tailWord_1713046).sum := by decide
  have hdescent : baseEnd_1713046 < baseStart_1713046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713055 : List Nat := [1, 1, 2, 5, 2, 2, 1, 3, 1, 4]
def baseStart_1713055 : Nat := 118140960795 + 1713055 * 2 ^ 59
def prefixEnd_1713055 : Nat := 4983230072969 + 3 ^ 40 * 1713055 * 2
def baseEnd_1713055 : Nat := 586413735058600265422873

theorem tailTrace_1713055 : CollatzResearch.WordTrace tailWord_1713055 prefixEnd_1713055 586413735058600265422873 := by
  unfold tailWord_1713055
  simp only [CollatzResearch.WordTrace]
  refine ⟨62480248808901776346700619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41653499205934517564467079 62480248808901776346700619)
  ·
    refine ⟨93720373213352664520050929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62480248808901776346700619 93720373213352664520050929)
    ·
      refine ⟨70290279910014498390038197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93720373213352664520050929 70290279910014498390038197)
      ·
        refine ⟨6589713741563859224066081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70290279910014498390038197 6589713741563859224066081)
        ·
          refine ⟨4942285306172894418049561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6589713741563859224066081 4942285306172894418049561)
          ·
            refine ⟨3706713979629670813537171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4942285306172894418049561 3706713979629670813537171)
            ·
              refine ⟨5560070969444506220305757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3706713979629670813537171 5560070969444506220305757)
              ·
                refine ⟨2085026613541689832614659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5560070969444506220305757 2085026613541689832614659)
                ·
                  refine ⟨3127539920312534748921989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085026613541689832614659 3127539920312534748921989)
                  ·
                    refine ⟨586413735058600265422873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3127539920312534748921989 586413735058600265422873)
                    ·
                      rfl

theorem cell22_1713055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 3, 1, 4].length) (baseStart_1713055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713055 prefixEnd_1713055 := by exact prefixLift 1713055
  have htrace : WordTrace (prefixWord ++ tailWord_1713055) baseStart_1713055 baseEnd_1713055 := by
    simpa [prefixWord, tailWord_1713055, baseEnd_1713055] using wordTrace_append hprefix tailTrace_1713055
  have hstable : (prefixWord ++ tailWord_1713055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713055).length < 2 ^ (prefixWord ++ tailWord_1713055).sum := by decide
  have hdescent : baseEnd_1713055 < baseStart_1713055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713068 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 4, 3]
def baseStart_1713068 : Nat := 118140960795 + 1713068 * 2 ^ 59
def prefixEnd_1713068 : Nat := 4983230072969 + 3 ^ 40 * 1713068 * 2
def baseEnd_1713068 : Nat := 586418185224272564847833

theorem tailTrace_1713068 : CollatzResearch.WordTrace tailWord_1713068 prefixEnd_1713068 586418185224272564847833 := by
  unfold tailWord_1713068
  simp only [CollatzResearch.WordTrace]
  refine ⟨31240361478927339783461929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41653815305236453044615905 31240361478927339783461929)
  ·
    refine ⟨23430271109195504837596447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31240361478927339783461929 23430271109195504837596447)
    ·
      refine ⟨35145406663793257256394671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23430271109195504837596447 35145406663793257256394671)
      ·
        refine ⟨52718109995689885884592007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35145406663793257256394671 52718109995689885884592007)
        ·
          refine ⟨79077164993534828826888011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52718109995689885884592007 79077164993534828826888011)
          ·
            refine ⟨118615747490302243240332017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79077164993534828826888011 118615747490302243240332017)
            ·
              refine ⟨88961810617726682430249013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118615747490302243240332017 88961810617726682430249013)
              ·
                refine ⟨8340169745411876477835845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88961810617726682430249013 8340169745411876477835845)
                ·
                  refine ⟨1563781827264726839594221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8340169745411876477835845 1563781827264726839594221)
                  ·
                    refine ⟨586418185224272564847833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1563781827264726839594221 586418185224272564847833)
                    ·
                      rfl

theorem cell22_1713068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 4, 3].length) (baseStart_1713068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713068 prefixEnd_1713068 := by exact prefixLift 1713068
  have htrace : WordTrace (prefixWord ++ tailWord_1713068) baseStart_1713068 baseEnd_1713068 := by
    simpa [prefixWord, tailWord_1713068, baseEnd_1713068] using wordTrace_append hprefix tailTrace_1713068
  have hstable : (prefixWord ++ tailWord_1713068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713068).length < 2 ^ (prefixWord ++ tailWord_1713068).sum := by decide
  have hdescent : baseEnd_1713068 < baseStart_1713068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713140 : List Nat := [2, 6, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_1713140 : Nat := 118140960795 + 1713140 * 2 ^ 59
def prefixEnd_1713140 : Nat := 4983230072969 + 3 ^ 40 * 1713140 * 2
def baseEnd_1713140 : Nat := 586442832295688377047613

theorem tailTrace_1713140 : CollatzResearch.WordTrace tailWord_1713140 prefixEnd_1713140 586442832295688377047613 := by
  unfold tailWord_1713140
  simp only [CollatzResearch.WordTrace]
  refine ⟨31241674506796917931772437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41655566009062557242363249 31241674506796917931772437)
  ·
    refine ⟨1464453492506105528051833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31241674506796917931772437 1464453492506105528051833)
    ·
      refine ⟨1098340119379579146038875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1464453492506105528051833 1098340119379579146038875)
      ·
        refine ⟨1647510179069368719058313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098340119379579146038875 1647510179069368719058313)
        ·
          refine ⟨1235632634302026539293735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1647510179069368719058313 1235632634302026539293735)
          ·
            refine ⟨1853448951453039808940603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1235632634302026539293735 1853448951453039808940603)
            ·
              refine ⟨2780173427179559713410905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1853448951453039808940603 2780173427179559713410905)
              ·
                refine ⟨2085130070384669785058179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780173427179559713410905 2085130070384669785058179)
                ·
                  refine ⟨3127695105577004677587269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2085130070384669785058179 3127695105577004677587269)
                  ·
                    refine ⟨586442832295688377047613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3127695105577004677587269 586442832295688377047613)
                    ·
                      rfl

theorem cell22_1713140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_1713140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713140 prefixEnd_1713140 := by exact prefixLift 1713140
  have htrace : WordTrace (prefixWord ++ tailWord_1713140) baseStart_1713140 baseEnd_1713140 := by
    simpa [prefixWord, tailWord_1713140, baseEnd_1713140] using wordTrace_append hprefix tailTrace_1713140
  have hstable : (prefixWord ++ tailWord_1713140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713140).length < 2 ^ (prefixWord ++ tailWord_1713140).sum := by decide
  have hdescent : baseEnd_1713140 < baseStart_1713140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713265 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 5, 3]
def baseStart_1713265 : Nat := 118140960795 + 1713265 * 2 ^ 59
def prefixEnd_1713265 : Nat := 4983230072969 + 3 ^ 40 * 1713265 * 2
def baseEnd_1713265 : Nat := 586485622350229717672229

theorem tailTrace_1713265 : CollatzResearch.WordTrace tailWord_1713265 prefixEnd_1713265 586485622350229717672229 := by
  unfold tailWord_1713265
  simp only [CollatzResearch.WordTrace]
  refine ⟨62487908138140982211845249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41658605425427321474563499 62487908138140982211845249)
  ·
    refine ⟨46865931103605736658883937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62487908138140982211845249 46865931103605736658883937)
    ·
      refine ⟨35149448327704302494162953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46865931103605736658883937 35149448327704302494162953)
      ·
        refine ⟨26362086245778226870622215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35149448327704302494162953 26362086245778226870622215)
        ·
          refine ⟨39543129368667340305933323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26362086245778226870622215 39543129368667340305933323)
          ·
            refine ⟨59314694053001010458899985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39543129368667340305933323 59314694053001010458899985)
            ·
              refine ⟨44486020539750757844174989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59314694053001010458899985 44486020539750757844174989)
              ·
                refine ⟨16682257702406534191565621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44486020539750757844174989 16682257702406534191565621)
                ·
                  refine ⟨1563961659600612580459277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16682257702406534191565621 1563961659600612580459277)
                  ·
                    refine ⟨586485622350229717672229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1563961659600612580459277 586485622350229717672229)
                    ·
                      rfl

theorem cell22_1713265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 5, 3].length) (baseStart_1713265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713265 prefixEnd_1713265 := by exact prefixLift 1713265
  have htrace : WordTrace (prefixWord ++ tailWord_1713265) baseStart_1713265 baseEnd_1713265 := by
    simpa [prefixWord, tailWord_1713265, baseEnd_1713265] using wordTrace_append hprefix tailTrace_1713265
  have hstable : (prefixWord ++ tailWord_1713265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713265).length < 2 ^ (prefixWord ++ tailWord_1713265).sum := by decide
  have hdescent : baseEnd_1713265 < baseStart_1713265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713370 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 1, 6]
def baseStart_1713370 : Nat := 118140960795 + 1713370 * 2 ^ 59
def prefixEnd_1713370 : Nat := 4983230072969 + 3 ^ 40 * 1713370 * 2
def baseEnd_1713370 : Nat := 586521565996044443796907

theorem tailTrace_1713370 : CollatzResearch.WordTrace tailWord_1713370 prefixEnd_1713370 586521565996044443796907 := by
  unfold tailWord_1713370
  simp only [CollatzResearch.WordTrace]
  refine ⟨15622934450690146286104391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41661158535173723429611709 15622934450690146286104391)
  ·
    refine ⟨23434401676035219429156587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15622934450690146286104391 23434401676035219429156587)
    ·
      refine ⟨35151602514052829143734881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23434401676035219429156587 35151602514052829143734881)
      ·
        refine ⟨26363701885539621857801161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35151602514052829143734881 26363701885539621857801161)
        ·
          refine ⟨19772776414154716393350871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26363701885539621857801161 19772776414154716393350871)
          ·
            refine ⟨29659164621232074590026307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19772776414154716393350871 29659164621232074590026307)
            ·
              refine ⟨44488746931848111885039461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29659164621232074590026307 44488746931848111885039461)
              ·
                refine ⟨8341640049721520978444899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44488746931848111885039461 8341640049721520978444899)
                ·
                  refine ⟨12512460074582281467667349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8341640049721520978444899 12512460074582281467667349)
                  ·
                    refine ⟨586521565996044443796907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12512460074582281467667349 586521565996044443796907)
                    ·
                      rfl

theorem cell22_1713370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 1, 6].length) (baseStart_1713370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713370 prefixEnd_1713370 := by exact prefixLift 1713370
  have htrace : WordTrace (prefixWord ++ tailWord_1713370) baseStart_1713370 baseEnd_1713370 := by
    simpa [prefixWord, tailWord_1713370, baseEnd_1713370] using wordTrace_append hprefix tailTrace_1713370
  have hstable : (prefixWord ++ tailWord_1713370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713370).length < 2 ^ (prefixWord ++ tailWord_1713370).sum := by decide
  have hdescent : baseEnd_1713370 < baseStart_1713370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713387 : List Nat := [1, 1, 1, 1, 2, 6, 3, 1, 2, 4]
def baseStart_1713387 : Nat := 118140960795 + 1713387 * 2 ^ 59
def prefixEnd_1713387 : Nat := 4983230072969 + 3 ^ 40 * 1713387 * 2
def baseEnd_1713387 : Nat := 586527385443462066121855

theorem tailTrace_1713387 : CollatzResearch.WordTrace tailWord_1713387 prefixEnd_1713387 586527385443462066121855 := by
  unfold tailWord_1713387
  simp only [CollatzResearch.WordTrace]
  refine ⟨62492357843698997047786415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41661571895799331365190943 62492357843698997047786415)
  ·
    refine ⟨93738536765548495571679623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62492357843698997047786415 93738536765548495571679623)
    ·
      refine ⟨140607805148322743357519435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93738536765548495571679623 140607805148322743357519435)
      ·
        refine ⟨210911707722484115036279153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140607805148322743357519435 210911707722484115036279153)
        ·
          refine ⟨158183780791863086277209365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210911707722484115036279153 158183780791863086277209365)
          ·
            refine ⟨7414864724618582169244189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 158183780791863086277209365 7414864724618582169244189)
            ·
              refine ⟨2780574271731968313466571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7414864724618582169244189 2780574271731968313466571)
              ·
                refine ⟨4170861407597952470199857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2780574271731968313466571 4170861407597952470199857)
                ·
                  refine ⟨3128146055698464352649893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4170861407597952470199857 3128146055698464352649893)
                  ·
                    refine ⟨586527385443462066121855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3128146055698464352649893 586527385443462066121855)
                    ·
                      rfl

theorem cell22_1713387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 4].length) (baseStart_1713387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713387 prefixEnd_1713387 := by exact prefixLift 1713387
  have htrace : WordTrace (prefixWord ++ tailWord_1713387) baseStart_1713387 baseEnd_1713387 := by
    simpa [prefixWord, tailWord_1713387, baseEnd_1713387] using wordTrace_append hprefix tailTrace_1713387
  have hstable : (prefixWord ++ tailWord_1713387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713387).length < 2 ^ (prefixWord ++ tailWord_1713387).sum := by decide
  have hdescent : baseEnd_1713387 < baseStart_1713387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713406 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 2, 3]
def baseStart_1713406 : Nat := 118140960795 + 1713406 * 2 ^ 59
def prefixEnd_1713406 : Nat := 4983230072969 + 3 ^ 40 * 1713406 * 2
def baseEnd_1713406 : Nat := 586533889531752349896797

theorem tailTrace_1713406 : CollatzResearch.WordTrace tailWord_1713406 prefixEnd_1713406 586533889531752349896797 := by
  unfold tailWord_1713406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7811631353828770411591009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41662033887086775528485381 7811631353828770411591009)
  ·
    refine ⟨5858723515371577808693257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7811631353828770411591009 5858723515371577808693257)
    ·
      refine ⟨4394042636528683356519943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5858723515371577808693257 4394042636528683356519943)
      ·
        refine ⟨6591063954793025034779915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394042636528683356519943 6591063954793025034779915)
        ·
          refine ⟨9886595932189537552169873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6591063954793025034779915 9886595932189537552169873)
          ·
            refine ⟨7414946949142153164127405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9886595932189537552169873 7414946949142153164127405)
            ·
              refine ⟨2780605105928307436547777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7414946949142153164127405 2780605105928307436547777)
              ·
                refine ⟨2085453829446230577410833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2780605105928307436547777 2085453829446230577410833)
                ·
                  refine ⟨1564090372084672933058125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2085453829446230577410833 1564090372084672933058125)
                  ·
                    refine ⟨586533889531752349896797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1564090372084672933058125 586533889531752349896797)
                    ·
                      rfl

theorem cell22_1713406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_1713406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713406 prefixEnd_1713406 := by exact prefixLift 1713406
  have htrace : WordTrace (prefixWord ++ tailWord_1713406) baseStart_1713406 baseEnd_1713406 := by
    simpa [prefixWord, tailWord_1713406, baseEnd_1713406] using wordTrace_append hprefix tailTrace_1713406
  have hstable : (prefixWord ++ tailWord_1713406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713406).length < 2 ^ (prefixWord ++ tailWord_1713406).sum := by decide
  have hdescent : baseEnd_1713406 < baseStart_1713406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713434 : List Nat := [3, 1, 1, 3, 3, 1, 2, 2, 3, 3]
def baseStart_1713434 : Nat := 118140960795 + 1713434 * 2 ^ 59
def prefixEnd_1713434 : Nat := 4983230072969 + 3 ^ 40 * 1713434 * 2
def baseEnd_1713434 : Nat := 586543474503969610196711

theorem tailTrace_1713434 : CollatzResearch.WordTrace tailWord_1713434 prefixEnd_1713434 586543474503969610196711 := by
  unfold tailWord_1713434
  simp only [CollatzResearch.WordTrace]
  refine ⟨15623518018632181018686839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41662714716352482716498237 15623518018632181018686839)
  ·
    refine ⟨23435277027948271528030259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15623518018632181018686839 23435277027948271528030259)
    ·
      refine ⟨35152915541922407292045389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23435277027948271528030259 35152915541922407292045389)
      ·
        refine ⟨13182343328220902734517021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35152915541922407292045389 13182343328220902734517021)
        ·
          refine ⟨4943378748082838525443883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13182343328220902734517021 4943378748082838525443883)
          ·
            refine ⟨7415068122124257788165825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943378748082838525443883 7415068122124257788165825)
            ·
              refine ⟨5561301091593193341124369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7415068122124257788165825 5561301091593193341124369)
              ·
                refine ⟨4170975818694895005843277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5561301091593193341124369 4170975818694895005843277)
                ·
                  refine ⟨1564115932010585627191229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4170975818694895005843277 1564115932010585627191229)
                  ·
                    refine ⟨586543474503969610196711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1564115932010585627191229 586543474503969610196711)
                    ·
                      rfl

theorem cell22_1713434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_1713434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713434 prefixEnd_1713434 := by exact prefixLift 1713434
  have htrace : WordTrace (prefixWord ++ tailWord_1713434) baseStart_1713434 baseEnd_1713434 := by
    simpa [prefixWord, tailWord_1713434, baseEnd_1713434] using wordTrace_append hprefix tailTrace_1713434
  have hstable : (prefixWord ++ tailWord_1713434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713434).length < 2 ^ (prefixWord ++ tailWord_1713434).sum := by decide
  have hdescent : baseEnd_1713434 < baseStart_1713434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713468 : List Nat := [2, 2, 2, 2, 1, 4, 3, 2, 1, 3]
def baseStart_1713468 : Nat := 118140960795 + 1713468 * 2 ^ 59
def prefixEnd_1713468 : Nat := 4983230072969 + 3 ^ 40 * 1713468 * 2
def baseEnd_1713468 : Nat := 586555113398804854846607

theorem tailTrace_1713468 : CollatzResearch.WordTrace tailWord_1713468 prefixEnd_1713468 586555113398804854846607 := by
  unfold tailWord_1713468
  simp only [CollatzResearch.WordTrace]
  refine ⟨31247656078202773940742529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41663541437603698587656705 31247656078202773940742529)
  ·
    refine ⟨23435742058652080455556897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31247656078202773940742529 23435742058652080455556897)
    ·
      refine ⟨17576806543989060341667673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23435742058652080455556897 17576806543989060341667673)
      ·
        refine ⟨13182604907991795256250755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17576806543989060341667673 13182604907991795256250755)
        ·
          refine ⟨19773907361987692884376133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13182604907991795256250755 19773907361987692884376133)
          ·
            refine ⟨3707607630372692415820525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19773907361987692884376133 3707607630372692415820525)
            ·
              refine ⟨1390352861389759655932697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3707607630372692415820525 1390352861389759655932697)
              ·
                refine ⟨1042764646042319741949523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1390352861389759655932697 1042764646042319741949523)
                ·
                  refine ⟨1564146969063479612924285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1042764646042319741949523 1564146969063479612924285)
                  ·
                    refine ⟨586555113398804854846607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1564146969063479612924285 586555113398804854846607)
                    ·
                      rfl

theorem cell22_1713468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 3, 2, 1, 3].length) (baseStart_1713468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713468 prefixEnd_1713468 := by exact prefixLift 1713468
  have htrace : WordTrace (prefixWord ++ tailWord_1713468) baseStart_1713468 baseEnd_1713468 := by
    simpa [prefixWord, tailWord_1713468, baseEnd_1713468] using wordTrace_append hprefix tailTrace_1713468
  have hstable : (prefixWord ++ tailWord_1713468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713468).length < 2 ^ (prefixWord ++ tailWord_1713468).sum := by decide
  have hdescent : baseEnd_1713468 < baseStart_1713468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713492 : List Nat := [2, 4, 1, 1, 2, 1, 2, 1, 8]
def baseStart_1713492 : Nat := 118140960795 + 1713492 * 2 ^ 59
def prefixEnd_1713492 : Nat := 4983230072969 + 3 ^ 40 * 1713492 * 2
def baseEnd_1713492 : Nat := 195521109696425597415511

theorem tailTrace_1713492 : CollatzResearch.WordTrace tailWord_1713492 prefixEnd_1713492 195521109696425597415511 := by
  unfold tailWord_1713492
  simp only [CollatzResearch.WordTrace]
  refine ⟨31248093754159299990179365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41664125005545733320239153 31248093754159299990179365)
  ·
    refine ⟨5859017578904868748158631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31248093754159299990179365 5859017578904868748158631)
    ·
      refine ⟨8788526368357303122237947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5859017578904868748158631 8788526368357303122237947)
      ·
        refine ⟨13182789552535954683356921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8788526368357303122237947 13182789552535954683356921)
        ·
          refine ⟨9887092164401966012517691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13182789552535954683356921 9887092164401966012517691)
          ·
            refine ⟨14830638246602949018776537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9887092164401966012517691 14830638246602949018776537)
            ·
              refine ⟨11122978684952211764082403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14830638246602949018776537 11122978684952211764082403)
              ·
                refine ⟨16684468027428317646123605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11122978684952211764082403 16684468027428317646123605)
                ·
                  refine ⟨195521109696425597415511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16684468027428317646123605 195521109696425597415511)
                  ·
                    rfl

theorem cell22_1713492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_1713492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713492 prefixEnd_1713492 := by exact prefixLift 1713492
  have htrace : WordTrace (prefixWord ++ tailWord_1713492) baseStart_1713492 baseEnd_1713492 := by
    simpa [prefixWord, tailWord_1713492, baseEnd_1713492] using wordTrace_append hprefix tailTrace_1713492
  have hstable : (prefixWord ++ tailWord_1713492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713492).length < 2 ^ (prefixWord ++ tailWord_1713492).sum := by decide
  have hdescent : baseEnd_1713492 < baseStart_1713492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713507 : List Nat := [1, 1, 1, 5, 2, 2, 1, 1, 3, 5]
def baseStart_1713507 : Nat := 118140960795 + 1713507 * 2 ^ 59
def prefixEnd_1713507 : Nat := 4983230072969 + 3 ^ 40 * 1713507 * 2
def baseEnd_1713507 : Nat := 586568463895821753121487

theorem tailTrace_1713507 : CollatzResearch.WordTrace tailWord_1713507 prefixEnd_1713507 586568463895821753121487 := by
  unfold tailWord_1713507
  simp only [CollatzResearch.WordTrace]
  refine ⟨62496734603264257542154775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41664489735509505028103183 62496734603264257542154775)
  ·
    refine ⟨93745101904896386313232163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62496734603264257542154775 93745101904896386313232163)
    ·
      refine ⟨140617652857344579469848245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93745101904896386313232163 140617652857344579469848245)
      ·
        refine ⟨13182904955376054325298273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140617652857344579469848245 13182904955376054325298273)
        ·
          refine ⟨9887178716532040743973705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13182904955376054325298273 9887178716532040743973705)
          ·
            refine ⟨7415384037399030557980279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9887178716532040743973705 7415384037399030557980279)
            ·
              refine ⟨11123076056098545836970419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7415384037399030557980279 11123076056098545836970419)
              ·
                refine ⟨16684614084147818755455629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11123076056098545836970419 16684614084147818755455629)
                ·
                  refine ⟨6256730281555432033295861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16684614084147818755455629 6256730281555432033295861)
                  ·
                    refine ⟨586568463895821753121487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6256730281555432033295861 586568463895821753121487)
                    ·
                      rfl

theorem cell22_1713507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 5].length) (baseStart_1713507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713507 prefixEnd_1713507 := by exact prefixLift 1713507
  have htrace : WordTrace (prefixWord ++ tailWord_1713507) baseStart_1713507 baseEnd_1713507 := by
    simpa [prefixWord, tailWord_1713507, baseEnd_1713507] using wordTrace_append hprefix tailTrace_1713507
  have hstable : (prefixWord ++ tailWord_1713507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713507).length < 2 ^ (prefixWord ++ tailWord_1713507).sum := by decide
  have hdescent : baseEnd_1713507 < baseStart_1713507 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713509 : List Nat := [1, 3, 1, 3, 1, 2, 2, 5, 4]
def baseStart_1713509 : Nat := 118140960795 + 1713509 * 2 ^ 59
def prefixEnd_1713509 : Nat := 4983230072969 + 3 ^ 40 * 1713509 * 2
def baseEnd_1713509 : Nat := 195523049512231471523827

theorem tailTrace_1713509 : CollatzResearch.WordTrace tailWord_1713509 prefixEnd_1713509 195523049512231471523827 := by
  unfold tailWord_1713509
  simp only [CollatzResearch.WordTrace]
  refine ⟨62496807549257011883727581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41664538366171341255818387 62496807549257011883727581)
  ·
    refine ⟨23436302830971379456397843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62496807549257011883727581 23436302830971379456397843)
    ·
      refine ⟨35154454246457069184596765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23436302830971379456397843 35154454246457069184596765)
      ·
        refine ⟨13182920342421400944223787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35154454246457069184596765 13182920342421400944223787)
        ·
          refine ⟨19774380513632101416335681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13182920342421400944223787 19774380513632101416335681)
          ·
            refine ⟨14830785385224076062251761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19774380513632101416335681 14830785385224076062251761)
            ·
              refine ⟨11123089038918057046688821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14830785385224076062251761 11123089038918057046688821)
              ·
                refine ⟨1042789597398567848127077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11123089038918057046688821 1042789597398567848127077)
                ·
                  refine ⟨195523049512231471523827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1042789597398567848127077 195523049512231471523827)
                  ·
                    rfl

theorem cell22_1713509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 5, 4].length) (baseStart_1713509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713509 prefixEnd_1713509 := by exact prefixLift 1713509
  have htrace : WordTrace (prefixWord ++ tailWord_1713509) baseStart_1713509 baseEnd_1713509 := by
    simpa [prefixWord, tailWord_1713509, baseEnd_1713509] using wordTrace_append hprefix tailTrace_1713509
  have hstable : (prefixWord ++ tailWord_1713509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713509).length < 2 ^ (prefixWord ++ tailWord_1713509).sum := by decide
  have hdescent : baseEnd_1713509 < baseStart_1713509 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713556 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 2, 4]
def baseStart_1713556 : Nat := 118140960795 + 1713556 * 2 ^ 59
def prefixEnd_1713556 : Nat := 4983230072969 + 3 ^ 40 * 1713556 * 2
def baseEnd_1713556 : Nat := 586585237597201958646337

theorem tailTrace_1713556 : CollatzResearch.WordTrace tailWord_1713556 prefixEnd_1713556 586585237597201958646337 := by
  unfold tailWord_1713556
  simp only [CollatzResearch.WordTrace]
  refine ⟨31249260890043369455344261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41665681186724492607125681 31249260890043369455344261)
  ·
    refine ⟨5859236416883131772877049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31249260890043369455344261 5859236416883131772877049)
    ·
      refine ⟨4394427312662348829657787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5859236416883131772877049 4394427312662348829657787)
      ·
        refine ⟨6591640968993523244486681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4394427312662348829657787 6591640968993523244486681)
        ·
          refine ⟨4943730726745142433365011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6591640968993523244486681 4943730726745142433365011)
          ·
            refine ⟨7415596090117713650047517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4943730726745142433365011 7415596090117713650047517)
            ·
              refine ⟨2780848533794142618767819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7415596090117713650047517 2780848533794142618767819)
              ·
                refine ⟨4171272800691213928151729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2780848533794142618767819 4171272800691213928151729)
                ·
                  refine ⟨3128454600518410446113797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4171272800691213928151729 3128454600518410446113797)
                  ·
                    refine ⟨586585237597201958646337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3128454600518410446113797 586585237597201958646337)
                    ·
                      rfl

theorem cell22_1713556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 2, 4].length) (baseStart_1713556 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713556 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713556 prefixEnd_1713556 := by exact prefixLift 1713556
  have htrace : WordTrace (prefixWord ++ tailWord_1713556) baseStart_1713556 baseEnd_1713556 := by
    simpa [prefixWord, tailWord_1713556, baseEnd_1713556] using wordTrace_append hprefix tailTrace_1713556
  have hstable : (prefixWord ++ tailWord_1713556).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713556).length < 2 ^ (prefixWord ++ tailWord_1713556).sum := by decide
  have hdescent : baseEnd_1713556 < baseStart_1713556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713676 : List Nat := [2, 2, 1, 2, 5, 1, 1, 2, 1, 5]
def baseStart_1713676 : Nat := 118140960795 + 1713676 * 2 ^ 59
def prefixEnd_1713676 : Nat := 4983230072969 + 3 ^ 40 * 1713676 * 2
def baseEnd_1713676 : Nat := 586626316049561645645969

theorem tailTrace_1713676 : CollatzResearch.WordTrace tailWord_1713676 prefixEnd_1713676 586626316049561645645969 := by
  unfold tailWord_1713676
  simp only [CollatzResearch.WordTrace]
  refine ⟨31251449269825999702528441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41668599026434666270037921 31251449269825999702528441)
  ·
    refine ⟨23438586952369499776896331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31251449269825999702528441 23438586952369499776896331)
    ·
      refine ⟨35157880428554249665344497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23438586952369499776896331 35157880428554249665344497)
      ·
        refine ⟨26368410321415687249008373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35157880428554249665344497 26368410321415687249008373)
        ·
          refine ⟨2472038467632720679594535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26368410321415687249008373 2472038467632720679594535)
          ·
            refine ⟨3708057701449081019391803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472038467632720679594535 3708057701449081019391803)
            ·
              refine ⟨5562086552173621529087705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708057701449081019391803 5562086552173621529087705)
              ·
                refine ⟨4171564914130216146815779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5562086552173621529087705 4171564914130216146815779)
                ·
                  refine ⟨6257347371195324220223669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4171564914130216146815779 6257347371195324220223669)
                  ·
                    refine ⟨586626316049561645645969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6257347371195324220223669 586626316049561645645969)
                    ·
                      rfl

theorem cell22_1713676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 5, 1, 1, 2, 1, 5].length) (baseStart_1713676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713676 prefixEnd_1713676 := by exact prefixLift 1713676
  have htrace : WordTrace (prefixWord ++ tailWord_1713676) baseStart_1713676 baseEnd_1713676 := by
    simpa [prefixWord, tailWord_1713676, baseEnd_1713676] using wordTrace_append hprefix tailTrace_1713676
  have hstable : (prefixWord ++ tailWord_1713676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713676).length < 2 ^ (prefixWord ++ tailWord_1713676).sum := by decide
  have hdescent : baseEnd_1713676 < baseStart_1713676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713693 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 2, 3]
def baseStart_1713693 : Nat := 118140960795 + 1713693 * 2 ^ 59
def prefixEnd_1713693 : Nat := 4983230072969 + 3 ^ 40 * 1713693 * 2
def baseEnd_1713693 : Nat := 586632135496979267970917

theorem tailTrace_1713693 : CollatzResearch.WordTrace tailWord_1713693 prefixEnd_1713693 586632135496979267970917 := by
  unfold tailWord_1713693
  simp only [CollatzResearch.WordTrace]
  refine ⟨62503518580590411308425733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41669012387060274205617155 62503518580590411308425733)
  ·
    refine ⟨11719409733860702120329825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62503518580590411308425733 11719409733860702120329825)
    ·
      refine ⟨8789557300395526590247369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11719409733860702120329825 8789557300395526590247369)
      ·
        refine ⟨6592167975296644942685527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8789557300395526590247369 6592167975296644942685527)
        ·
          refine ⟨9888251962944967414028291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6592167975296644942685527 9888251962944967414028291)
          ·
            refine ⟨14832377944417451121042437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9888251962944967414028291 14832377944417451121042437)
            ·
              refine ⟨2781070864578272085195457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14832377944417451121042437 2781070864578272085195457)
              ·
                refine ⟨2085803148433704063896593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2781070864578272085195457 2085803148433704063896593)
                ·
                  refine ⟨1564352361325278047922445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2085803148433704063896593 1564352361325278047922445)
                  ·
                    refine ⟨586632135496979267970917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1564352361325278047922445 586632135496979267970917)
                    ·
                      rfl

theorem cell22_1713693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 2, 3].length) (baseStart_1713693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713693 prefixEnd_1713693 := by exact prefixLift 1713693
  have htrace : WordTrace (prefixWord ++ tailWord_1713693) baseStart_1713693 baseEnd_1713693 := by
    simpa [prefixWord, tailWord_1713693, baseEnd_1713693] using wordTrace_append hprefix tailTrace_1713693
  have hstable : (prefixWord ++ tailWord_1713693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713693).length < 2 ^ (prefixWord ++ tailWord_1713693).sum := by decide
  have hdescent : baseEnd_1713693 < baseStart_1713693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713721 : List Nat := [1, 2, 1, 5, 1, 2, 1, 1, 5, 3]
def baseStart_1713721 : Nat := 118140960795 + 1713721 * 2 ^ 59
def prefixEnd_1713721 : Nat := 4983230072969 + 3 ^ 40 * 1713721 * 2
def baseEnd_1713721 : Nat := 586641720469196528270831

theorem tailTrace_1713721 : CollatzResearch.WordTrace tailWord_1713721 prefixEnd_1713721 586641720469196528270831 := by
  unfold tailWord_1713721
  simp only [CollatzResearch.WordTrace]
  refine ⟨62504539824488972090445017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41669693216325981393630011 62504539824488972090445017)
  ·
    refine ⟨46878404868366729067833763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62504539824488972090445017 46878404868366729067833763)
    ·
      refine ⟨70317607302550093601750645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46878404868366729067833763 70317607302550093601750645)
      ·
        refine ⟨6592275684614071275164123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70317607302550093601750645 6592275684614071275164123)
        ·
          refine ⟨9888413526921106912746185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6592275684614071275164123 9888413526921106912746185)
          ·
            refine ⟨7416310145190830184559639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9888413526921106912746185 7416310145190830184559639)
            ·
              refine ⟨11124465217786245276839459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7416310145190830184559639 11124465217786245276839459)
              ·
                refine ⟨16686697826679367915259189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11124465217786245276839459 16686697826679367915259189)
                ·
                  refine ⟨1564377921251190742055549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16686697826679367915259189 1564377921251190742055549)
                  ·
                    refine ⟨586641720469196528270831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1564377921251190742055549 586641720469196528270831)
                    ·
                      rfl

theorem cell22_1713721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 3].length) (baseStart_1713721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713721 prefixEnd_1713721 := by exact prefixLift 1713721
  have htrace : WordTrace (prefixWord ++ tailWord_1713721) baseStart_1713721 baseEnd_1713721 := by
    simpa [prefixWord, tailWord_1713721, baseEnd_1713721] using wordTrace_append hprefix tailTrace_1713721
  have hstable : (prefixWord ++ tailWord_1713721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713721).length < 2 ^ (prefixWord ++ tailWord_1713721).sum := by decide
  have hdescent : baseEnd_1713721 < baseStart_1713721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713725 : List Nat := [1, 4, 1, 3, 4, 1, 1, 1, 2, 4]
def baseStart_1713725 : Nat := 118140960795 + 1713725 * 2 ^ 59
def prefixEnd_1713725 : Nat := 4983230072969 + 3 ^ 40 * 1713725 * 2
def baseEnd_1713725 : Nat := 586643089750941851170819

theorem tailTrace_1713725 : CollatzResearch.WordTrace tailWord_1713725 prefixEnd_1713725 586643089750941851170819 := by
  unfold tailWord_1713725
  simp only [CollatzResearch.WordTrace]
  refine ⟨62504685716474480773590629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41669790477649653849060419 62504685716474480773590629)
  ·
    refine ⟨11719628571838965145048243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62504685716474480773590629 11719628571838965145048243)
    ·
      refine ⟨17579442857758447717572365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11719628571838965145048243 17579442857758447717572365)
      ·
        refine ⟨6592291071659417894089637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17579442857758447717572365 6592291071659417894089637)
        ·
          refine ⟨1236054575936140855141807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6592291071659417894089637 1236054575936140855141807)
          ·
            refine ⟨1854081863904211282712711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1236054575936140855141807 1854081863904211282712711)
            ·
              refine ⟨2781122795856316924069067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1854081863904211282712711 2781122795856316924069067)
              ·
                refine ⟨4171684193784475386103601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781122795856316924069067 4171684193784475386103601)
                ·
                  refine ⟨3128763145338356539577701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4171684193784475386103601 3128763145338356539577701)
                  ·
                    refine ⟨586643089750941851170819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3128763145338356539577701 586643089750941851170819)
                    ·
                      rfl

theorem cell22_1713725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 1, 2, 4].length) (baseStart_1713725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713725 prefixEnd_1713725 := by exact prefixLift 1713725
  have htrace : WordTrace (prefixWord ++ tailWord_1713725) baseStart_1713725 baseEnd_1713725 := by
    simpa [prefixWord, tailWord_1713725, baseEnd_1713725] using wordTrace_append hprefix tailTrace_1713725
  have hstable : (prefixWord ++ tailWord_1713725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713725).length < 2 ^ (prefixWord ++ tailWord_1713725).sum := by decide
  have hdescent : baseEnd_1713725 < baseStart_1713725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713751 : List Nat := [1, 1, 3, 2, 2, 3, 3, 2, 5]
def baseStart_1713751 : Nat := 118140960795 + 1713751 * 2 ^ 59
def prefixEnd_1713751 : Nat := 4983230072969 + 3 ^ 40 * 1713751 * 2
def baseEnd_1713751 : Nat := 195550663360762150006913

theorem tailTrace_1713751 : CollatzResearch.WordTrace tailWord_1713751 prefixEnd_1713751 195550663360762150006913 := by
  unfold tailWord_1713751
  simp only [CollatzResearch.WordTrace]
  refine ⟨62505634014380287214037107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41670422676253524809358071 62505634014380287214037107)
  ·
    refine ⟨93758451021570430821055661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62505634014380287214037107 93758451021570430821055661)
    ·
      refine ⟨35159419133088911557895873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93758451021570430821055661 35159419133088911557895873)
      ·
        refine ⟨26369564349816683668421905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35159419133088911557895873 26369564349816683668421905)
        ·
          refine ⟨19777173262362512751316429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26369564349816683668421905 19777173262362512751316429)
          ·
            refine ⟨7416439973385942281743661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19777173262362512751316429 7416439973385942281743661)
            ·
              refine ⟨2781164990019728355653873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7416439973385942281743661 2781164990019728355653873)
              ·
                refine ⟨2085873742514796266740405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2781164990019728355653873 2085873742514796266740405)
                ·
                  refine ⟨195550663360762150006913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2085873742514796266740405 195550663360762150006913)
                  ·
                    rfl

theorem cell22_1713751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 3, 2, 5].length) (baseStart_1713751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713751 prefixEnd_1713751 := by exact prefixLift 1713751
  have htrace : WordTrace (prefixWord ++ tailWord_1713751) baseStart_1713751 baseEnd_1713751 := by
    simpa [prefixWord, tailWord_1713751, baseEnd_1713751] using wordTrace_append hprefix tailTrace_1713751
  have hstable : (prefixWord ++ tailWord_1713751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713751).length < 2 ^ (prefixWord ++ tailWord_1713751).sum := by decide
  have hdescent : baseEnd_1713751 < baseStart_1713751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713809 : List Nat := [1, 2, 2, 1, 1, 1, 1, 4, 3, 6]
def baseStart_1713809 : Nat := 118140960795 + 1713809 * 2 ^ 59
def prefixEnd_1713809 : Nat := 4983230072969 + 3 ^ 40 * 1713809 * 2
def baseEnd_1713809 : Nat := 586671844667593632070561

theorem tailTrace_1713809 : CollatzResearch.WordTrace tailWord_1713809 prefixEnd_1713809 586671844667593632070561 := by
  unfold tailWord_1713809
  simp only [CollatzResearch.WordTrace]
  refine ⟨62507749448170163119648481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41671832965446775413098987 62507749448170163119648481)
  ·
    refine ⟨46880812086127622339736361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62507749448170163119648481 46880812086127622339736361)
    ·
      refine ⟨35160609064595716754802271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46880812086127622339736361 35160609064595716754802271)
      ·
        refine ⟨52740913596893575132203407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35160609064595716754802271 52740913596893575132203407)
        ·
          refine ⟨79111370395340362698305111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52740913596893575132203407 79111370395340362698305111)
          ·
            refine ⟨118667055593010544047457667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79111370395340362698305111 118667055593010544047457667)
            ·
              refine ⟨178000583389515816071186501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118667055593010544047457667 178000583389515816071186501)
              ·
                refine ⟨33375109385534215513347469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 178000583389515816071186501 33375109385534215513347469)
                ·
                  refine ⟨12515666019575330817505301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33375109385534215513347469 12515666019575330817505301)
                  ·
                    refine ⟨586671844667593632070561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12515666019575330817505301 586671844667593632070561)
                    ·
                      rfl

theorem cell22_1713809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 6].length) (baseStart_1713809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713809 prefixEnd_1713809 := by exact prefixLift 1713809
  have htrace : WordTrace (prefixWord ++ tailWord_1713809) baseStart_1713809 baseEnd_1713809 := by
    simpa [prefixWord, tailWord_1713809, baseEnd_1713809] using wordTrace_append hprefix tailTrace_1713809
  have hstable : (prefixWord ++ tailWord_1713809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713809).length < 2 ^ (prefixWord ++ tailWord_1713809).sum := by decide
  have hdescent : baseEnd_1713809 < baseStart_1713809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713832 : List Nat := [2, 1, 7, 1, 1, 1, 1, 1, 3, 4]
def baseStart_1713832 : Nat := 118140960795 + 1713832 * 2 ^ 59
def prefixEnd_1713832 : Nat := 4983230072969 + 3 ^ 40 * 1713832 * 2
def baseEnd_1713832 : Nat := 586679718037629238745491

theorem tailTrace_1713832 : CollatzResearch.WordTrace tailWord_1713832 prefixEnd_1713832 586679718037629238745491 := by
  unfold tailWord_1713832
  simp only [CollatzResearch.WordTrace]
  refine ⟨31254294163543419023867875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41672392218057892031823833 31254294163543419023867875)
  ·
    refine ⟨46881441245315128535801813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31254294163543419023867875 46881441245315128535801813)
    ·
      refine ⟨1098783779187073325057855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 46881441245315128535801813 1098783779187073325057855)
      ·
        refine ⟨1648175668780609987586783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1098783779187073325057855 1648175668780609987586783)
        ·
          refine ⟨2472263503170914981380175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1648175668780609987586783 2472263503170914981380175)
          ·
            refine ⟨3708395254756372472070263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472263503170914981380175 3708395254756372472070263)
            ·
              refine ⟨5562592882134558708105395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3708395254756372472070263 5562592882134558708105395)
              ·
                refine ⟨8343889323201838062158093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5562592882134558708105395 8343889323201838062158093)
                ·
                  refine ⟨3128958496200689273309285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8343889323201838062158093 3128958496200689273309285)
                  ·
                    refine ⟨586679718037629238745491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3128958496200689273309285 586679718037629238745491)
                    ·
                      rfl

theorem cell22_1713832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_1713832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713832 prefixEnd_1713832 := by exact prefixLift 1713832
  have htrace : WordTrace (prefixWord ++ tailWord_1713832) baseStart_1713832 baseEnd_1713832 := by
    simpa [prefixWord, tailWord_1713832, baseEnd_1713832] using wordTrace_append hprefix tailTrace_1713832
  have hstable : (prefixWord ++ tailWord_1713832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713832).length < 2 ^ (prefixWord ++ tailWord_1713832).sum := by decide
  have hdescent : baseEnd_1713832 < baseStart_1713832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713931 : List Nat := [1, 1, 1, 1, 5, 1, 3, 3, 6]
def baseStart_1713931 : Nat := 118140960795 + 1713931 * 2 ^ 59
def prefixEnd_1713931 : Nat := 4983230072969 + 3 ^ 40 * 1713931 * 2
def baseEnd_1713931 : Nat := 195571202586941993506729

theorem tailTrace_1713931 : CollatzResearch.WordTrace tailWord_1713931 prefixEnd_1713931 195571202586941993506729 := by
  unfold tailWord_1713931
  simp only [CollatzResearch.WordTrace]
  refine ⟨62512199153728177955589647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41674799435818785303726431 62512199153728177955589647)
  ·
    refine ⟨93768298730592266933384471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62512199153728177955589647 93768298730592266933384471)
    ·
      refine ⟨140652448095888400400076707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93768298730592266933384471 140652448095888400400076707)
      ·
        refine ⟨210978672143832600600115061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140652448095888400400076707 210978672143832600600115061)
        ·
          refine ⟨19779250513484306306260787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210978672143832600600115061 19779250513484306306260787)
          ·
            refine ⟨29668875770226459459391181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19779250513484306306260787 29668875770226459459391181)
            ·
              refine ⟨11125828413834922297271693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29668875770226459459391181 11125828413834922297271693)
              ·
                refine ⟨4172185655188095861476885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11125828413834922297271693 4172185655188095861476885)
                ·
                  refine ⟨195571202586941993506729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4172185655188095861476885 195571202586941993506729)
                  ·
                    rfl

theorem cell22_1713931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 3, 6].length) (baseStart_1713931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713931 prefixEnd_1713931 := by exact prefixLift 1713931
  have htrace : WordTrace (prefixWord ++ tailWord_1713931) baseStart_1713931 baseEnd_1713931 := by
    simpa [prefixWord, tailWord_1713931, baseEnd_1713931] using wordTrace_append hprefix tailTrace_1713931
  have hstable : (prefixWord ++ tailWord_1713931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713931).length < 2 ^ (prefixWord ++ tailWord_1713931).sum := by decide
  have hdescent : baseEnd_1713931 < baseStart_1713931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713976 : List Nat := [2, 1, 2, 1, 3, 3, 10]
def baseStart_1713976 : Nat := 118140960795 + 1713976 * 2 ^ 59
def prefixEnd_1713976 : Nat := 4983230072969 + 3 ^ 40 * 1713976 * 2
def baseEnd_1713976 : Nat := 21730704154831883820187

theorem tailTrace_1713976 : CollatzResearch.WordTrace tailWord_1713976 prefixEnd_1713976 21730704154831883820187 := by
  unfold tailWord_1713976
  simp only [CollatzResearch.WordTrace]
  refine ⟨31256920219282575320488891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41675893625710100427318521 31256920219282575320488891)
  ·
    refine ⟨46885380328923862980733337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31256920219282575320488891 46885380328923862980733337)
    ·
      refine ⟨35164035246692897235550003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46885380328923862980733337 35164035246692897235550003)
      ·
        refine ⟨52746052870039345853325005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35164035246692897235550003 52746052870039345853325005)
        ·
          refine ⟨19779769826264754694996877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52746052870039345853325005 19779769826264754694996877)
          ·
            refine ⟨7417413684849283010623829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19779769826264754694996877 7417413684849283010623829)
            ·
              refine ⟨21730704154831883820187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7417413684849283010623829 21730704154831883820187)
              ·
                rfl

theorem cell22_1713976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 10].length) (baseStart_1713976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713976 prefixEnd_1713976 := by exact prefixLift 1713976
  have htrace : WordTrace (prefixWord ++ tailWord_1713976) baseStart_1713976 baseEnd_1713976 := by
    simpa [prefixWord, tailWord_1713976, baseEnd_1713976] using wordTrace_append hprefix tailTrace_1713976
  have hstable : (prefixWord ++ tailWord_1713976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713976).length < 2 ^ (prefixWord ++ tailWord_1713976).sum := by decide
  have hdescent : baseEnd_1713976 < baseStart_1713976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1713978 : List Nat := [3, 1, 1, 1, 5, 1, 1, 1, 4, 4]
def baseStart_1713978 : Nat := 118140960795 + 1713978 * 2 ^ 59
def prefixEnd_1713978 : Nat := 4983230072969 + 3 ^ 40 * 1713978 * 2
def baseEnd_1713978 : Nat := 586729696821333524595043

theorem tailTrace_1713978 : CollatzResearch.WordTrace tailWord_1713978 prefixEnd_1713978 586729696821333524595043 := by
  unfold tailWord_1713978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15628478346139476245637647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41675942256371936655033725 15628478346139476245637647)
  ·
    refine ⟨23442717519209214368456471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15628478346139476245637647 23442717519209214368456471)
    ·
      refine ⟨35164076278813821552684707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23442717519209214368456471 35164076278813821552684707)
      ·
        refine ⟨52746114418220732329027061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35164076278813821552684707 52746114418220732329027061)
        ·
          refine ⟨4944948226708193655846287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52746114418220732329027061 4944948226708193655846287)
          ·
            refine ⟨7417422340062290483769431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4944948226708193655846287 7417422340062290483769431)
            ·
              refine ⟨11126133510093435725654147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7417422340062290483769431 11126133510093435725654147)
              ·
                refine ⟨16689200265140153588481221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11126133510093435725654147 16689200265140153588481221)
                ·
                  refine ⟨3129225049713778797840229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16689200265140153588481221 3129225049713778797840229)
                  ·
                    refine ⟨586729696821333524595043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3129225049713778797840229 586729696821333524595043)
                    ·
                      rfl

theorem cell22_1713978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 4, 4].length) (baseStart_1713978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1713978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1713978 prefixEnd_1713978 := by exact prefixLift 1713978
  have htrace : WordTrace (prefixWord ++ tailWord_1713978) baseStart_1713978 baseEnd_1713978 := by
    simpa [prefixWord, tailWord_1713978, baseEnd_1713978] using wordTrace_append hprefix tailTrace_1713978
  have hstable : (prefixWord ++ tailWord_1713978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1713978).length < 2 ^ (prefixWord ++ tailWord_1713978).sum := by decide
  have hdescent : baseEnd_1713978 < baseStart_1713978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1713978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714012 : List Nat := [2, 2, 4, 2, 2, 1, 2, 1, 2, 4]
def baseStart_1714012 : Nat := 118140960795 + 1714012 * 2 ^ 59
def prefixEnd_1714012 : Nat := 4983230072969 + 3 ^ 40 * 1714012 * 2
def baseEnd_1714012 : Nat := 586741335716168769244939

theorem tailTrace_1714012 : CollatzResearch.WordTrace tailWord_1714012 prefixEnd_1714012 586741335716168769244939 := by
  unfold tailWord_1714012
  simp only [CollatzResearch.WordTrace]
  refine ⟨31257576733217364394644145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41676768977623152526192193 31257576733217364394644145)
  ·
    refine ⟨23443182549913023295983109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31257576733217364394644145 23443182549913023295983109)
    ·
      refine ⟨4395596728108691867996833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23443182549913023295983109 4395596728108691867996833)
      ·
        refine ⟨3296697546081518900997625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4395596728108691867996833 3296697546081518900997625)
        ·
          refine ⟨2472523159561139175748219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3296697546081518900997625 2472523159561139175748219)
          ·
            refine ⟨3708784739341708763622329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2472523159561139175748219 3708784739341708763622329)
            ·
              refine ⟨2781588554506281572716747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3708784739341708763622329 2781588554506281572716747)
              ·
                refine ⟨4172382831759422359075121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2781588554506281572716747 4172382831759422359075121)
                ·
                  refine ⟨3129287123819566769306341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4172382831759422359075121 3129287123819566769306341)
                  ·
                    refine ⟨586741335716168769244939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3129287123819566769306341 586741335716168769244939)
                    ·
                      rfl

theorem cell22_1714012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_1714012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714012 prefixEnd_1714012 := by exact prefixLift 1714012
  have htrace : WordTrace (prefixWord ++ tailWord_1714012) baseStart_1714012 baseEnd_1714012 := by
    simpa [prefixWord, tailWord_1714012, baseEnd_1714012] using wordTrace_append hprefix tailTrace_1714012
  have hstable : (prefixWord ++ tailWord_1714012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714012).length < 2 ^ (prefixWord ++ tailWord_1714012).sum := by decide
  have hdescent : baseEnd_1714012 < baseStart_1714012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714053 : List Nat := [1, 3, 1, 1, 3, 2, 3, 1, 2, 5]
def baseStart_1714053 : Nat := 118140960795 + 1714053 * 2 ^ 59
def prefixEnd_1714053 : Nat := 4983230072969 + 3 ^ 40 * 1714053 * 2
def baseEnd_1714053 : Nat := 586755370854058328969813

theorem tailTrace_1714053 : CollatzResearch.WordTrace tailWord_1714053 prefixEnd_1714053 586755370854058328969813 := by
  unfold tailWord_1714053
  simp only [CollatzResearch.WordTrace]
  refine ⟨62516648859286192791530813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41677765906190795194353875 62516648859286192791530813)
  ·
    refine ⟨23443743322232322296824055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62516648859286192791530813 23443743322232322296824055)
    ·
      refine ⟨35165614983348483445236083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23443743322232322296824055 35165614983348483445236083)
      ·
        refine ⟨52748422475022725167854125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35165614983348483445236083 52748422475022725167854125)
        ·
          refine ⟨19780658428133521937945297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52748422475022725167854125 19780658428133521937945297)
          ·
            refine ⟨14835493821100141453458973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19780658428133521937945297 14835493821100141453458973)
            ·
              refine ⟨5563310182912553045047115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14835493821100141453458973 5563310182912553045047115)
              ·
                refine ⟨8344965274368829567570673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5563310182912553045047115 8344965274368829567570673)
                ·
                  refine ⟨6258723955776622175678005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8344965274368829567570673 6258723955776622175678005)
                  ·
                    refine ⟨586755370854058328969813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6258723955776622175678005 586755370854058328969813)
                    ·
                      rfl

theorem cell22_1714053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_1714053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714053 prefixEnd_1714053 := by exact prefixLift 1714053
  have htrace : WordTrace (prefixWord ++ tailWord_1714053) baseStart_1714053 baseEnd_1714053 := by
    simpa [prefixWord, tailWord_1714053, baseEnd_1714053] using wordTrace_append hprefix tailTrace_1714053
  have hstable : (prefixWord ++ tailWord_1714053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714053).length < 2 ^ (prefixWord ++ tailWord_1714053).sum := by decide
  have hdescent : baseEnd_1714053 < baseStart_1714053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714098 : List Nat := [3, 2, 1, 1, 1, 1, 1, 4, 3, 5]
def baseStart_1714098 : Nat := 118140960795 + 1714098 * 2 ^ 59
def prefixEnd_1714098 : Nat := 4983230072969 + 3 ^ 40 * 1714098 * 2
def baseEnd_1714098 : Nat := 586770775273693211594675

theorem tailTrace_1714098 : CollatzResearch.WordTrace tailWord_1714098 prefixEnd_1714098 586770775273693211594675 := by
  unfold tailWord_1714098
  simp only [CollatzResearch.WordTrace]
  refine ⟨15629572536030791369229737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41678860096082110317945965 15629572536030791369229737)
  ·
    refine ⟨11722179402023093526922303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15629572536030791369229737 11722179402023093526922303)
    ·
      refine ⟨17583269103034640290383455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11722179402023093526922303 17583269103034640290383455)
      ·
        refine ⟨26374903654551960435575183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17583269103034640290383455 26374903654551960435575183)
        ·
          refine ⟨39562355481827940653362775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26374903654551960435575183 39562355481827940653362775)
          ·
            refine ⟨59343533222741910980044163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39562355481827940653362775 59343533222741910980044163)
            ·
              refine ⟨89015299834112866470066245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59343533222741910980044163 89015299834112866470066245)
              ·
                refine ⟨16690368718896162463137421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89015299834112866470066245 16690368718896162463137421)
                ·
                  refine ⟨6258888269586060923676533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16690368718896162463137421 6258888269586060923676533)
                  ·
                    refine ⟨586770775273693211594675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6258888269586060923676533 586770775273693211594675)
                    ·
                      rfl

theorem cell22_1714098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 4, 3, 5].length) (baseStart_1714098 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714098 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714098 prefixEnd_1714098 := by exact prefixLift 1714098
  have htrace : WordTrace (prefixWord ++ tailWord_1714098) baseStart_1714098 baseEnd_1714098 := by
    simpa [prefixWord, tailWord_1714098, baseEnd_1714098] using wordTrace_append hprefix tailTrace_1714098
  have hstable : (prefixWord ++ tailWord_1714098).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714098).length < 2 ^ (prefixWord ++ tailWord_1714098).sum := by decide
  have hdescent : baseEnd_1714098 < baseStart_1714098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714222 : List Nat := [4, 1, 3, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1714222 : Nat := 118140960795 + 1714222 * 2 ^ 59
def prefixEnd_1714222 : Nat := 4983230072969 + 3 ^ 40 * 1714222 * 2
def baseEnd_1714222 : Nat := 586813223007798221494295

theorem tailTrace_1714222 : CollatzResearch.WordTrace tailWord_1714222 prefixEnd_1714222 586813223007798221494295 := by
  unfold tailWord_1714222
  simp only [CollatzResearch.WordTrace]
  refine ⟨7815351599459241831804115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41681875197115956436288613 7815351599459241831804115)
  ·
    refine ⟨11723027399188862747706173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7815351599459241831804115 11723027399188862747706173)
    ·
      refine ⟨4396135274695823530389815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11723027399188862747706173 4396135274695823530389815)
      ·
        refine ⟨6594202912043735295584723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4396135274695823530389815 6594202912043735295584723)
        ·
          refine ⟨9891304368065602943377085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6594202912043735295584723 9891304368065602943377085)
          ·
            refine ⟨3709239138024601103766407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9891304368065602943377085 3709239138024601103766407)
            ·
              refine ⟨5563858707036901655649611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709239138024601103766407 5563858707036901655649611)
              ·
                refine ⟨8345788060555352483474417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5563858707036901655649611 8345788060555352483474417)
                ·
                  refine ⟨6259341045416514362605813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8345788060555352483474417 6259341045416514362605813)
                  ·
                    refine ⟨586813223007798221494295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6259341045416514362605813 586813223007798221494295)
                    ·
                      rfl

theorem cell22_1714222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1714222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714222 prefixEnd_1714222 := by exact prefixLift 1714222
  have htrace : WordTrace (prefixWord ++ tailWord_1714222) baseStart_1714222 baseEnd_1714222 := by
    simpa [prefixWord, tailWord_1714222, baseEnd_1714222] using wordTrace_append hprefix tailTrace_1714222
  have hstable : (prefixWord ++ tailWord_1714222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714222).length < 2 ^ (prefixWord ++ tailWord_1714222).sum := by decide
  have hdescent : baseEnd_1714222 < baseStart_1714222 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714237 : List Nat := [1, 4, 1, 3, 1, 1, 2, 4, 1, 4]
def baseStart_1714237 : Nat := 118140960795 + 1714237 * 2 ^ 59
def prefixEnd_1714237 : Nat := 4983230072969 + 3 ^ 40 * 1714237 * 2
def baseEnd_1714237 : Nat := 586818357814343182369249

theorem tailTrace_1714237 : CollatzResearch.WordTrace tailWord_1714237 prefixEnd_1714237 586818357814343182369249 := by
  unfold tailWord_1714237
  simp only [CollatzResearch.WordTrace]
  refine ⟨62523359890619592216228965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41682239927079728144152643 62523359890619592216228965)
  ·
    refine ⟨11723129979491173540542931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62523359890619592216228965 11723129979491173540542931)
    ·
      refine ⟨17584694969236760310814397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11723129979491173540542931 17584694969236760310814397)
      ·
        refine ⟨6594260613463785116555399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17584694969236760310814397 6594260613463785116555399)
        ·
          refine ⟨9891390920195677674833099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6594260613463785116555399 9891390920195677674833099)
          ·
            refine ⟨14837086380293516512249649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9891390920195677674833099 14837086380293516512249649)
            ·
              refine ⟨11127814785220137384187237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14837086380293516512249649 11127814785220137384187237)
              ·
                refine ⟨2086465272228775759535107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11127814785220137384187237 2086465272228775759535107)
                ·
                  refine ⟨3129697908343163639302661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086465272228775759535107 3129697908343163639302661)
                  ·
                    refine ⟨586818357814343182369249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3129697908343163639302661 586818357814343182369249)
                    ·
                      rfl

theorem cell22_1714237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 2, 4, 1, 4].length) (baseStart_1714237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714237 prefixEnd_1714237 := by exact prefixLift 1714237
  have htrace : WordTrace (prefixWord ++ tailWord_1714237) baseStart_1714237 baseEnd_1714237 := by
    simpa [prefixWord, tailWord_1714237, baseEnd_1714237] using wordTrace_append hprefix tailTrace_1714237
  have hstable : (prefixWord ++ tailWord_1714237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714237).length < 2 ^ (prefixWord ++ tailWord_1714237).sum := by decide
  have hdescent : baseEnd_1714237 < baseStart_1714237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714252 : List Nat := [2, 2, 1, 3, 1, 1, 3, 5, 4]
def baseStart_1714252 : Nat := 118140960795 + 1714252 * 2 ^ 59
def prefixEnd_1714252 : Nat := 4983230072969 + 3 ^ 40 * 1714252 * 2
def baseEnd_1714252 : Nat := 195607830873629381081401

theorem tailTrace_1714252 : CollatzResearch.WordTrace tailWord_1714252 prefixEnd_1714252 195607830873629381081401 := by
  unfold tailWord_1714252
  simp only [CollatzResearch.WordTrace]
  refine ⟨31261953492782624889012505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41682604657043499852016673 31261953492782624889012505)
  ·
    refine ⟨23446465119586968666759379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31261953492782624889012505 23446465119586968666759379)
    ·
      refine ⟨35169697679380453000139069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23446465119586968666759379 35169697679380453000139069)
      ·
        refine ⟨13188636629767669875052151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35169697679380453000139069 13188636629767669875052151)
        ·
          refine ⟨19782954944651504812578227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13188636629767669875052151 19782954944651504812578227)
          ·
            refine ⟨29674432416977257218867341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19782954944651504812578227 29674432416977257218867341)
            ·
              refine ⟨11127912156366471457075253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29674432416977257218867341 11127912156366471457075253)
              ·
                refine ⟨1043241764659356699100805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11127912156366471457075253 1043241764659356699100805)
                ·
                  refine ⟨195607830873629381081401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1043241764659356699100805 195607830873629381081401)
                  ·
                    rfl

theorem cell22_1714252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 3, 5, 4].length) (baseStart_1714252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714252 prefixEnd_1714252 := by exact prefixLift 1714252
  have htrace : WordTrace (prefixWord ++ tailWord_1714252) baseStart_1714252 baseEnd_1714252 := by
    simpa [prefixWord, tailWord_1714252, baseEnd_1714252] using wordTrace_append hprefix tailTrace_1714252
  have hstable : (prefixWord ++ tailWord_1714252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714252).length < 2 ^ (prefixWord ++ tailWord_1714252).sum := by decide
  have hdescent : baseEnd_1714252 < baseStart_1714252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714254 : List Nat := [4, 1, 1, 1, 1, 4, 4, 1, 1, 4]
def baseStart_1714254 : Nat := 118140960795 + 1714254 * 2 ^ 59
def prefixEnd_1714254 : Nat := 4983230072969 + 3 ^ 40 * 1714254 * 2
def baseEnd_1714254 : Nat := 586824177261760804694197

theorem tailTrace_1714254 : CollatzResearch.WordTrace tailWord_1714254 prefixEnd_1714254 586824177261760804694197 := by
  unfold tailWord_1714254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7815497491444750514949727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41682653287705336079731877 7815497491444750514949727)
  ·
    refine ⟨11723246237167125772424591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7815497491444750514949727 11723246237167125772424591)
    ·
      refine ⟨17584869355750688658636887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11723246237167125772424591 17584869355750688658636887)
      ·
        refine ⟨26377304033626032987955331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17584869355750688658636887 26377304033626032987955331)
        ·
          refine ⟨39565956050439049481932997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26377304033626032987955331 39565956050439049481932997)
          ·
            refine ⟨7418616759457321777862437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39565956050439049481932997 7418616759457321777862437)
            ·
              refine ⟨1390990642398247833349207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7418616759457321777862437 1390990642398247833349207)
              ·
                refine ⟨2086485963597371750023811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1390990642398247833349207 2086485963597371750023811)
                ·
                  refine ⟨3129728945396057625035717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2086485963597371750023811 3129728945396057625035717)
                  ·
                    refine ⟨586824177261760804694197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3129728945396057625035717 586824177261760804694197)
                    ·
                      rfl

theorem cell22_1714254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 4, 1, 1, 4].length) (baseStart_1714254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714254 prefixEnd_1714254 := by exact prefixLift 1714254
  have htrace : WordTrace (prefixWord ++ tailWord_1714254) baseStart_1714254 baseEnd_1714254 := by
    simpa [prefixWord, tailWord_1714254, baseEnd_1714254] using wordTrace_append hprefix tailTrace_1714254
  have hstable : (prefixWord ++ tailWord_1714254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714254).length < 2 ^ (prefixWord ++ tailWord_1714254).sum := by decide
  have hdescent : baseEnd_1714254 < baseStart_1714254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714265 : List Nat := [1, 2, 1, 2, 2, 1, 4, 1, 4, 4]
def baseStart_1714265 : Nat := 118140960795 + 1714265 * 2 ^ 59
def prefixEnd_1714265 : Nat := 4983230072969 + 3 ^ 40 * 1714265 * 2
def baseEnd_1714265 : Nat := 586827942786560442669163

theorem tailTrace_1714265 : CollatzResearch.WordTrace tailWord_1714265 prefixEnd_1714265 586827942786560442669163 := by
  unfold tailWord_1714265
  simp only [CollatzResearch.WordTrace]
  refine ⟨62524381134518152998248249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41682920756345435332165499 62524381134518152998248249)
  ·
    refine ⟨46893285850888614748686187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62524381134518152998248249 46893285850888614748686187)
    ·
      refine ⟨70339928776332922123029281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46893285850888614748686187 70339928776332922123029281)
      ·
        refine ⟨52754946582249691592271961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70339928776332922123029281 52754946582249691592271961)
        ·
          refine ⟨39566209936687268694203971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52754946582249691592271961 39566209936687268694203971)
          ·
            refine ⟨59349314905030903041305957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39566209936687268694203971 59349314905030903041305957)
            ·
              refine ⟨11127996544693294320244867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59349314905030903041305957 11127996544693294320244867)
              ·
                refine ⟨16691994817039941480367301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11127996544693294320244867 16691994817039941480367301)
                ·
                  refine ⟨3129749028194989027568869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16691994817039941480367301 3129749028194989027568869)
                  ·
                    refine ⟨586827942786560442669163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3129749028194989027568869 586827942786560442669163)
                    ·
                      rfl

theorem cell22_1714265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 1, 4, 4].length) (baseStart_1714265 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714265 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714265 prefixEnd_1714265 := by exact prefixLift 1714265
  have htrace : WordTrace (prefixWord ++ tailWord_1714265) baseStart_1714265 baseEnd_1714265 := by
    simpa [prefixWord, tailWord_1714265, baseEnd_1714265] using wordTrace_append hprefix tailTrace_1714265
  have hstable : (prefixWord ++ tailWord_1714265).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714265).length < 2 ^ (prefixWord ++ tailWord_1714265).sum := by decide
  have hdescent : baseEnd_1714265 < baseStart_1714265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714269 : List Nat := [1, 4, 4, 1, 1, 2, 2, 1, 6]
def baseStart_1714269 : Nat := 118140960795 + 1714269 * 2 ^ 59
def prefixEnd_1714269 : Nat := 4983230072969 + 3 ^ 40 * 1714269 * 2
def baseEnd_1714269 : Nat := 195609770689435255189717

theorem tailTrace_1714269 : CollatzResearch.WordTrace tailWord_1714269 prefixEnd_1714269 195609770689435255189717 := by
  unfold tailWord_1714269
  simp only [CollatzResearch.WordTrace]
  refine ⟨62524527026503661681393861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41683018017669107787595907 62524527026503661681393861)
  ·
    refine ⟨11723348817469436565261349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62524527026503661681393861 11723348817469436565261349)
    ·
      refine ⟨2198127903275519355986503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11723348817469436565261349 2198127903275519355986503)
      ·
        refine ⟨3297191854913279033979755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2198127903275519355986503 3297191854913279033979755)
        ·
          refine ⟨4945787782369918550969633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3297191854913279033979755 4945787782369918550969633)
          ·
            refine ⟨3709340836777438913227225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4945787782369918550969633 3709340836777438913227225)
            ·
              refine ⟨2782005627583079184920419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3709340836777438913227225 2782005627583079184920419)
              ·
                refine ⟨4173008441374618777380629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782005627583079184920419 4173008441374618777380629)
                ·
                  refine ⟨195609770689435255189717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4173008441374618777380629 195609770689435255189717)
                  ·
                    rfl

theorem cell22_1714269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_1714269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714269 prefixEnd_1714269 := by exact prefixLift 1714269
  have htrace : WordTrace (prefixWord ++ tailWord_1714269) baseStart_1714269 baseEnd_1714269 := by
    simpa [prefixWord, tailWord_1714269, baseEnd_1714269] using wordTrace_append hprefix tailTrace_1714269
  have hstable : (prefixWord ++ tailWord_1714269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714269).length < 2 ^ (prefixWord ++ tailWord_1714269).sum := by decide
  have hdescent : baseEnd_1714269 < baseStart_1714269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714297 : List Nat := [1, 2, 1, 3, 4, 1, 4, 6]
def baseStart_1714297 : Nat := 118140960795 + 1714297 * 2 ^ 59
def prefixEnd_1714297 : Nat := 4983230072969 + 3 ^ 40 * 1714297 * 2
def baseEnd_1714297 : Nat := 65204321893391447318785

theorem tailTrace_1714297 : CollatzResearch.WordTrace tailWord_1714297 prefixEnd_1714297 65204321893391447318785 := by
  unfold tailWord_1714297
  simp only [CollatzResearch.WordTrace]
  refine ⟨62525548270402222463413145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41683698846934814975608763 62525548270402222463413145)
  ·
    refine ⟨46894161202801666847559859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62525548270402222463413145 46894161202801666847559859)
    ·
      refine ⟨70341241804202500271339789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46894161202801666847559859 70341241804202500271339789)
      ·
        refine ⟨26377965676575937601752421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70341241804202500271339789 26377965676575937601752421)
        ·
          refine ⟨4945868564357988300328579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26377965676575937601752421 4945868564357988300328579)
          ·
            refine ⟨7418802846536982450492869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4945868564357988300328579 7418802846536982450492869)
            ·
              refine ⟨1391025533725684209467413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7418802846536982450492869 1391025533725684209467413)
              ·
                refine ⟨65204321893391447318785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1391025533725684209467413 65204321893391447318785)
                ·
                  rfl

theorem cell22_1714297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 4, 6].length) (baseStart_1714297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714297 prefixEnd_1714297 := by exact prefixLift 1714297
  have htrace : WordTrace (prefixWord ++ tailWord_1714297) baseStart_1714297 baseEnd_1714297 := by
    simpa [prefixWord, tailWord_1714297, baseEnd_1714297] using wordTrace_append hprefix tailTrace_1714297
  have hstable : (prefixWord ++ tailWord_1714297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714297).length < 2 ^ (prefixWord ++ tailWord_1714297).sum := by decide
  have hdescent : baseEnd_1714297 < baseStart_1714297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714325 : List Nat := [1, 3, 2, 1, 1, 1, 3, 3, 7]
def baseStart_1714325 : Nat := 118140960795 + 1714325 * 2 ^ 59
def prefixEnd_1714325 : Nat := 4983230072969 + 3 ^ 40 * 1714325 * 2
def baseEnd_1714325 : Nat := 195616160670913428722993

theorem tailTrace_1714325 : CollatzResearch.WordTrace tailWord_1714325 prefixEnd_1714325 195616160670913428722993 := by
  unfold tailWord_1714325
  simp only [CollatzResearch.WordTrace]
  refine ⟨62526569514300783245432429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41684379676200522163621619 62526569514300783245432429)
  ·
    refine ⟨23447463567862793717037161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62526569514300783245432429 23447463567862793717037161)
    ·
      refine ⟨17585597675897095287777871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23447463567862793717037161 17585597675897095287777871)
      ·
        refine ⟨26378396513845642931666807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17585597675897095287777871 26378396513845642931666807)
        ·
          refine ⟨39567594770768464397500211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26378396513845642931666807 39567594770768464397500211)
          ·
            refine ⟨59351392156152696596250317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39567594770768464397500211 59351392156152696596250317)
            ·
              refine ⟨22256772058557261223593869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59351392156152696596250317 22256772058557261223593869)
              ·
                refine ⟨8346289521958972958847701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22256772058557261223593869 8346289521958972958847701)
                ·
                  refine ⟨195616160670913428722993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8346289521958972958847701 195616160670913428722993)
                  ·
                    rfl

theorem cell22_1714325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 3, 7].length) (baseStart_1714325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714325 prefixEnd_1714325 := by exact prefixLift 1714325
  have htrace : WordTrace (prefixWord ++ tailWord_1714325) baseStart_1714325 baseEnd_1714325 := by
    simpa [prefixWord, tailWord_1714325, baseEnd_1714325] using wordTrace_append hprefix tailTrace_1714325
  have hstable : (prefixWord ++ tailWord_1714325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714325).length < 2 ^ (prefixWord ++ tailWord_1714325).sum := by decide
  have hdescent : baseEnd_1714325 < baseStart_1714325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714329 : List Nat := [1, 2, 1, 2, 1, 2, 1, 8, 1, 3]
def baseStart_1714329 : Nat := 118140960795 + 1714329 * 2 ^ 59
def prefixEnd_1714329 : Nat := 4983230072969 + 3 ^ 40 * 1714329 * 2
def baseEnd_1714329 : Nat := 586849851294485609068967

theorem tailTrace_1714329 : CollatzResearch.WordTrace tailWord_1714329 prefixEnd_1714329 586849851294485609068967 := by
  unfold tailWord_1714329
  simp only [CollatzResearch.WordTrace]
  refine ⟨62526715406286291928578041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41684476937524194619052027 62526715406286291928578041)
  ·
    refine ⟨46895036554714718946433531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62526715406286291928578041 46895036554714718946433531)
    ·
      refine ⟨70342554832072078419650297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46895036554714718946433531 70342554832072078419650297)
      ·
        refine ⟨52756916124054058814737723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70342554832072078419650297 52756916124054058814737723)
        ·
          refine ⟨79135374186081088222106585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52756916124054058814737723 79135374186081088222106585)
          ·
            refine ⟨59351530639560816166579939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79135374186081088222106585 59351530639560816166579939)
            ·
              refine ⟨89027295959341224249869909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59351530639560816166579939 89027295959341224249869909)
              ·
                refine ⟨1043288624523529971678163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 89027295959341224249869909 1043288624523529971678163)
                ·
                  refine ⟨1564932936785294957517245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043288624523529971678163 1564932936785294957517245)
                  ·
                    refine ⟨586849851294485609068967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1564932936785294957517245 586849851294485609068967)
                    ·
                      rfl

theorem cell22_1714329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 8, 1, 3].length) (baseStart_1714329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714329 prefixEnd_1714329 := by exact prefixLift 1714329
  have htrace : WordTrace (prefixWord ++ tailWord_1714329) baseStart_1714329 baseEnd_1714329 := by
    simpa [prefixWord, tailWord_1714329, baseEnd_1714329] using wordTrace_append hprefix tailTrace_1714329
  have hstable : (prefixWord ++ tailWord_1714329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714329).length < 2 ^ (prefixWord ++ tailWord_1714329).sum := by decide
  have hdescent : baseEnd_1714329 < baseStart_1714329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714436 : List Nat := [2, 3, 2, 2, 3, 1, 1, 1, 4, 3]
def baseStart_1714436 : Nat := 118140960795 + 1714436 * 2 ^ 59
def prefixEnd_1714436 : Nat := 4983230072969 + 3 ^ 40 * 1714436 * 2
def baseEnd_1714436 : Nat := 586886479581172996643639

theorem tailTrace_1714436 : CollatzResearch.WordTrace tailWord_1714436 prefixEnd_1714436 586886479581172996643639 := by
  unfold tailWord_1714436
  simp only [CollatzResearch.WordTrace]
  refine ⟨31265309008449324601361581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41687078677932432801815441 31265309008449324601361581)
  ·
    refine ⟨11724490878168496725510593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31265309008449324601361581 11724490878168496725510593)
    ·
      refine ⟨8793368158626372544132945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11724490878168496725510593 8793368158626372544132945)
      ·
        refine ⟨6595026118969779408099709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8793368158626372544132945 6595026118969779408099709)
        ·
          refine ⟨2473134794613667278037391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6595026118969779408099709 2473134794613667278037391)
          ·
            refine ⟨3709702191920500917056087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473134794613667278037391 3709702191920500917056087)
            ·
              refine ⟨5564553287880751375584131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3709702191920500917056087 5564553287880751375584131)
              ·
                refine ⟨8346829931821127063376197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564553287880751375584131 8346829931821127063376197)
                ·
                  refine ⟨1565030612216461324383037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8346829931821127063376197 1565030612216461324383037)
                  ·
                    refine ⟨586886479581172996643639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565030612216461324383037 586886479581172996643639)
                    ·
                      rfl

theorem cell22_1714436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_1714436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714436 prefixEnd_1714436 := by exact prefixLift 1714436
  have htrace : WordTrace (prefixWord ++ tailWord_1714436) baseStart_1714436 baseEnd_1714436 := by
    simpa [prefixWord, tailWord_1714436, baseEnd_1714436] using wordTrace_append hprefix tailTrace_1714436
  have hstable : (prefixWord ++ tailWord_1714436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714436).length < 2 ^ (prefixWord ++ tailWord_1714436).sum := by decide
  have hdescent : baseEnd_1714436 < baseStart_1714436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714466 : List Nat := [3, 3, 1, 1, 3, 3, 2, 6]
def baseStart_1714466 : Nat := 118140960795 + 1714466 * 2 ^ 59
def prefixEnd_1714466 : Nat := 4983230072969 + 3 ^ 40 * 1714466 * 2
def baseEnd_1714466 : Nat := 65210749910473657599283

theorem tailTrace_1714466 : CollatzResearch.WordTrace tailWord_1714466 prefixEnd_1714466 65210749910473657599283 := by
  unfold tailWord_1714466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15632928051697491081578813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41687808137859976217543501 15632928051697491081578813)
  ·
    refine ⟨5862348019386559155592055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15632928051697491081578813 5862348019386559155592055)
    ·
      refine ⟨8793522029079838733388083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5862348019386559155592055 8793522029079838733388083)
      ·
        refine ⟨13190283043619758100082125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8793522029079838733388083 13190283043619758100082125)
        ·
          refine ⟨4946356141357409287530797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13190283043619758100082125 4946356141357409287530797)
          ·
            refine ⟨1854883553009028482824049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4946356141357409287530797 1854883553009028482824049)
            ·
              refine ⟨1391162664756771362118037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1854883553009028482824049 1391162664756771362118037)
              ·
                refine ⟨65210749910473657599283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1391162664756771362118037 65210749910473657599283)
                ·
                  rfl

theorem cell22_1714466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 2, 6].length) (baseStart_1714466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714466 prefixEnd_1714466 := by exact prefixLift 1714466
  have htrace : WordTrace (prefixWord ++ tailWord_1714466) baseStart_1714466 baseEnd_1714466 := by
    simpa [prefixWord, tailWord_1714466, baseEnd_1714466] using wordTrace_append hprefix tailTrace_1714466
  have hstable : (prefixWord ++ tailWord_1714466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714466).length < 2 ^ (prefixWord ++ tailWord_1714466).sum := by decide
  have hdescent : baseEnd_1714466 < baseStart_1714466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714494 : List Nat := [4, 2, 1, 2, 1, 2, 2, 1, 7]
def baseStart_1714494 : Nat := 118140960795 + 1714494 * 2 ^ 59
def prefixEnd_1714494 : Nat := 4983230072969 + 3 ^ 40 * 1714494 * 2
def baseEnd_1714494 : Nat := 195635444722160059564487

theorem tailTrace_1714494 : CollatzResearch.WordTrace tailWord_1714494 prefixEnd_1714494 195635444722160059564487 := by
  unfold tailWord_1714494
  simp only [CollatzResearch.WordTrace]
  refine ⟨7816591681336065638541817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41688488967125683405556357 7816591681336065638541817)
  ·
    refine ⟨5862443761002049228906363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7816591681336065638541817 5862443761002049228906363)
    ·
      refine ⟨8793665641503073843359545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5862443761002049228906363 8793665641503073843359545)
      ·
        refine ⟨6595249231127305382519659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8793665641503073843359545 6595249231127305382519659)
        ·
          refine ⟨9892873846690958073779489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595249231127305382519659 9892873846690958073779489)
          ·
            refine ⟨7419655385018218555334617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9892873846690958073779489 7419655385018218555334617)
            ·
              refine ⟨5564741538763663916500963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7419655385018218555334617 5564741538763663916500963)
              ·
                refine ⟨8347112308145495874751445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5564741538763663916500963 8347112308145495874751445)
                ·
                  refine ⟨195635444722160059564487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8347112308145495874751445 195635444722160059564487)
                  ·
                    rfl

theorem cell22_1714494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 1, 7].length) (baseStart_1714494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714494 prefixEnd_1714494 := by exact prefixLift 1714494
  have htrace : WordTrace (prefixWord ++ tailWord_1714494) baseStart_1714494 baseEnd_1714494 := by
    simpa [prefixWord, tailWord_1714494, baseEnd_1714494] using wordTrace_append hprefix tailTrace_1714494
  have hstable : (prefixWord ++ tailWord_1714494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714494).length < 2 ^ (prefixWord ++ tailWord_1714494).sum := by decide
  have hdescent : baseEnd_1714494 < baseStart_1714494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714522 : List Nat := [3, 1, 1, 2, 1, 2, 1, 3, 8]
def baseStart_1714522 : Nat := 118140960795 + 1714522 * 2 ^ 59
def prefixEnd_1714522 : Nat := 4983230072969 + 3 ^ 40 * 1714522 * 2
def baseEnd_1714522 : Nat := 195638639712899146331125

theorem tailTrace_1714522 : CollatzResearch.WordTrace tailWord_1714522 prefixEnd_1714522 195638639712899146331125 := by
  unfold tailWord_1714522
  simp only [CollatzResearch.WordTrace]
  refine ⟨15633438673646771472588455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41689169796391390593569213 15633438673646771472588455)
  ·
    refine ⟨23450158010470157208882683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15633438673646771472588455 23450158010470157208882683)
    ·
      refine ⟨35175237015705235813324025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23450158010470157208882683 35175237015705235813324025)
      ·
        refine ⟨26381427761778926859993019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35175237015705235813324025 26381427761778926859993019)
        ·
          refine ⟨39572141642668390289989529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26381427761778926859993019 39572141642668390289989529)
          ·
            refine ⟨29679106232001292717492147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39572141642668390289989529 29679106232001292717492147)
            ·
              refine ⟨44518659348001939076238221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29679106232001292717492147 44518659348001939076238221)
              ·
                refine ⟨16694497255500727153589333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44518659348001939076238221 16694497255500727153589333)
                ·
                  refine ⟨195638639712899146331125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16694497255500727153589333 195638639712899146331125)
                  ·
                    rfl

theorem cell22_1714522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 3, 8].length) (baseStart_1714522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714522 prefixEnd_1714522 := by exact prefixLift 1714522
  have htrace : WordTrace (prefixWord ++ tailWord_1714522) baseStart_1714522 baseEnd_1714522 := by
    simpa [prefixWord, tailWord_1714522, baseEnd_1714522] using wordTrace_append hprefix tailTrace_1714522
  have hstable : (prefixWord ++ tailWord_1714522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714522).length < 2 ^ (prefixWord ++ tailWord_1714522).sum := by decide
  have hdescent : baseEnd_1714522 < baseStart_1714522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714571 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 2, 3]
def baseStart_1714571 : Nat := 118140960795 + 1714571 * 2 ^ 59
def prefixEnd_1714571 : Nat := 4983230072969 + 3 ^ 40 * 1714571 * 2
def baseEnd_1714571 : Nat := 586932692840077644518225

theorem tailTrace_1714571 : CollatzResearch.WordTrace tailWord_1714571 prefixEnd_1714571 586932692840077644518225 := by
  unfold tailWord_1714571
  simp only [CollatzResearch.WordTrace]
  refine ⟨62535541871409567258887567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41690361247606378172591711 62535541871409567258887567)
  ·
    refine ⟨93803312807114350888331351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62535541871409567258887567 93803312807114350888331351)
    ·
      refine ⟨140704969210671526332497027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93803312807114350888331351 140704969210671526332497027)
      ·
        refine ⟨211057453816007289498745541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140704969210671526332497027 211057453816007289498745541)
        ·
          refine ⟨39573272590501366781014789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211057453816007289498745541 39573272590501366781014789)
          ·
            refine ⟨7419988610719006271440273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39573272590501366781014789 7419988610719006271440273)
            ·
              refine ⟨5564991458039254703580205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7419988610719006271440273 5564991458039254703580205)
              ·
                refine ⟨2086871796764720513842577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5564991458039254703580205 2086871796764720513842577)
                ·
                  refine ⟨1565153847573540385381933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2086871796764720513842577 1565153847573540385381933)
                  ·
                    refine ⟨586932692840077644518225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565153847573540385381933 586932692840077644518225)
                    ·
                      rfl

theorem cell22_1714571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 2, 3].length) (baseStart_1714571 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714571 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714571 prefixEnd_1714571 := by exact prefixLift 1714571
  have htrace : WordTrace (prefixWord ++ tailWord_1714571) baseStart_1714571 baseEnd_1714571 := by
    simpa [prefixWord, tailWord_1714571, baseEnd_1714571] using wordTrace_append hprefix tailTrace_1714571
  have hstable : (prefixWord ++ tailWord_1714571).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714571).length < 2 ^ (prefixWord ++ tailWord_1714571).sum := by decide
  have hdescent : baseEnd_1714571 < baseStart_1714571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714586 : List Nat := [3, 1, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_1714586 : Nat := 118140960795 + 1714586 * 2 ^ 59
def prefixEnd_1714586 : Nat := 4983230072969 + 3 ^ 40 * 1714586 * 2
def baseEnd_1714586 : Nat := 586937827646622605393179

theorem tailTrace_1714586 : CollatzResearch.WordTrace tailWord_1714586 prefixEnd_1714586 586937827646622605393179 := by
  unfold tailWord_1714586
  simp only [CollatzResearch.WordTrace]
  refine ⟨15634022241588806205170903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41690725977570149880455741 15634022241588806205170903)
  ·
    refine ⟨23451033362383209307756355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15634022241588806205170903 23451033362383209307756355)
    ·
      refine ⟨35176550043574813961634533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23451033362383209307756355 35176550043574813961634533)
      ·
        refine ⟨6595603133170277617806475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35176550043574813961634533 6595603133170277617806475)
        ·
          refine ⟨9893404699755416426709713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595603133170277617806475 9893404699755416426709713)
          ·
            refine ⟨7420053524816562320032285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9893404699755416426709713 7420053524816562320032285)
            ·
              refine ⟨2782520071806210870012107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7420053524816562320032285 2782520071806210870012107)
              ·
                refine ⟨4173780107709316305018161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2782520071806210870012107 4173780107709316305018161)
                ·
                  refine ⟨3130335080781987228763621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4173780107709316305018161 3130335080781987228763621)
                  ·
                    refine ⟨586937827646622605393179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3130335080781987228763621 586937827646622605393179)
                    ·
                      rfl

theorem cell22_1714586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_1714586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714586 prefixEnd_1714586 := by exact prefixLift 1714586
  have htrace : WordTrace (prefixWord ++ tailWord_1714586) baseStart_1714586 baseEnd_1714586 := by
    simpa [prefixWord, tailWord_1714586, baseEnd_1714586] using wordTrace_append hprefix tailTrace_1714586
  have hstable : (prefixWord ++ tailWord_1714586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714586).length < 2 ^ (prefixWord ++ tailWord_1714586).sum := by decide
  have hdescent : baseEnd_1714586 < baseStart_1714586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714590 : List Nat := [4, 3, 1, 2, 1, 2, 2, 3, 4]
def baseStart_1714590 : Nat := 118140960795 + 1714590 * 2 ^ 59
def prefixEnd_1714590 : Nat := 4983230072969 + 3 ^ 40 * 1714590 * 2
def baseEnd_1714590 : Nat := 195646398976122642764389

theorem tailTrace_1714590 : CollatzResearch.WordTrace tailWord_1714590 prefixEnd_1714590 195646398976122642764389 := by
  unfold tailWord_1714590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7817029357292591687978653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41690823238893822335886149 7817029357292591687978653)
  ·
    refine ⟨2931386008984721882991995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7817029357292591687978653 2931386008984721882991995)
    ·
      refine ⟨4397079013477082824487993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2931386008984721882991995 4397079013477082824487993)
      ·
        refine ⟨3297809260107812118365995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4397079013477082824487993 3297809260107812118365995)
        ·
          refine ⟨4946713890161718177548993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3297809260107812118365995 4946713890161718177548993)
          ·
            refine ⟨3710035417621288633161745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4946713890161718177548993 3710035417621288633161745)
            ·
              refine ⟨2782526563215966474871309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3710035417621288633161745 2782526563215966474871309)
              ·
                refine ⟨1043447461205987428076741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2782526563215966474871309 1043447461205987428076741)
                ·
                  refine ⟨195646398976122642764389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1043447461205987428076741 195646398976122642764389)
                  ·
                    rfl

theorem cell22_1714590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 2, 3, 4].length) (baseStart_1714590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714590 prefixEnd_1714590 := by exact prefixLift 1714590
  have htrace : WordTrace (prefixWord ++ tailWord_1714590) baseStart_1714590 baseEnd_1714590 := by
    simpa [prefixWord, tailWord_1714590, baseEnd_1714590] using wordTrace_append hprefix tailTrace_1714590
  have hstable : (prefixWord ++ tailWord_1714590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714590).length < 2 ^ (prefixWord ++ tailWord_1714590).sum := by decide
  have hdescent : baseEnd_1714590 < baseStart_1714590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714646 : List Nat := [5, 2, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1714646 : Nat := 118140960795 + 1714646 * 2 ^ 59
def prefixEnd_1714646 : Nat := 4983230072969 + 3 ^ 40 * 1714646 * 2
def baseEnd_1714646 : Nat := 195652788957600816297665

theorem tailTrace_1714646 : CollatzResearch.WordTrace tailWord_1714646 prefixEnd_1714646 195652788957600816297665 := by
  unfold tailWord_1714646
  simp only [CollatzResearch.WordTrace]
  refine ⟨3908642334133615941741737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41692184897425236711911861 3908642334133615941741737)
  ·
    refine ⟨2931481750600211956306303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3908642334133615941741737 2931481750600211956306303)
    ·
      refine ⟨4397222625900317934459455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2931481750600211956306303 4397222625900317934459455)
      ·
        refine ⟨6595833938850476901689183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4397222625900317934459455 6595833938850476901689183)
        ·
          refine ⟨9893750908275715352533775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6595833938850476901689183 9893750908275715352533775)
          ·
            refine ⟨14840626362413573028800663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9893750908275715352533775 14840626362413573028800663)
            ·
              refine ⟨22260939543620359543200995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14840626362413573028800663 22260939543620359543200995)
              ·
                refine ⟨33391409315430539314801493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22260939543620359543200995 33391409315430539314801493)
                ·
                  refine ⟨195652788957600816297665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33391409315430539314801493 195652788957600816297665)
                  ·
                    rfl

theorem cell22_1714646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1714646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714646 prefixEnd_1714646 := by exact prefixLift 1714646
  have htrace : WordTrace (prefixWord ++ tailWord_1714646) baseStart_1714646 baseEnd_1714646 := by
    simpa [prefixWord, tailWord_1714646, baseEnd_1714646] using wordTrace_append hprefix tailTrace_1714646
  have hstable : (prefixWord ++ tailWord_1714646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714646).length < 2 ^ (prefixWord ++ tailWord_1714646).sum := by decide
  have hdescent : baseEnd_1714646 < baseStart_1714646 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714721 : List Nat := [1, 2, 3, 2, 2, 1, 1, 4, 2, 4]
def baseStart_1714721 : Nat := 118140960795 + 1714721 * 2 ^ 59
def prefixEnd_1714721 : Nat := 4983230072969 + 3 ^ 40 * 1714721 * 2
def baseEnd_1714721 : Nat := 586984040905527253267765

theorem tailTrace_1714721 : CollatzResearch.WordTrace tailWord_1714721 prefixEnd_1714721 586984040905527253267765 := by
  unfold tailWord_1714721
  simp only [CollatzResearch.WordTrace]
  refine ⟨62541012820866142876848017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41694008547244095251232011 62541012820866142876848017)
  ·
    refine ⟨46905759615649607157636013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62541012820866142876848017 46905759615649607157636013)
    ·
      refine ⟨17589659855868602684113505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46905759615649607157636013 17589659855868602684113505)
      ·
        refine ⟨13192244891901452013085129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17589659855868602684113505 13192244891901452013085129)
        ·
          refine ⟨9894183668926089009813847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13192244891901452013085129 9894183668926089009813847)
          ·
            refine ⟨14841275503389133514720771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9894183668926089009813847 14841275503389133514720771)
            ·
              refine ⟨22261913255083700272081157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14841275503389133514720771 22261913255083700272081157)
              ·
                refine ⟨4174108735328193801015217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22261913255083700272081157 4174108735328193801015217)
                ·
                  refine ⟨3130581551496145350761413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4174108735328193801015217 3130581551496145350761413)
                  ·
                    refine ⟨586984040905527253267765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3130581551496145350761413 586984040905527253267765)
                    ·
                      rfl

theorem cell22_1714721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 1, 4, 2, 4].length) (baseStart_1714721 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714721 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714721 prefixEnd_1714721 := by exact prefixLift 1714721
  have htrace : WordTrace (prefixWord ++ tailWord_1714721) baseStart_1714721 baseEnd_1714721 := by
    simpa [prefixWord, tailWord_1714721, baseEnd_1714721] using wordTrace_append hprefix tailTrace_1714721
  have hstable : (prefixWord ++ tailWord_1714721).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714721).length < 2 ^ (prefixWord ++ tailWord_1714721).sum := by decide
  have hdescent : baseEnd_1714721 < baseStart_1714721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714723 : List Nat := [1, 1, 1, 4, 4, 1, 1, 4, 2, 3]
def baseStart_1714723 : Nat := 118140960795 + 1714723 * 2 ^ 59
def prefixEnd_1714723 : Nat := 4983230072969 + 3 ^ 40 * 1714723 * 2
def baseEnd_1714723 : Nat := 586984725546399914717759

theorem tailTrace_1714723 : CollatzResearch.WordTrace tailWord_1714723 prefixEnd_1714723 586984725546399914717759 := by
  unfold tailWord_1714723
  simp only [CollatzResearch.WordTrace]
  refine ⟨62541085766858897218420823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41694057177905931478947215 62541085766858897218420823)
  ·
    refine ⟨93811628650288345827631235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62541085766858897218420823 93811628650288345827631235)
    ·
      refine ⟨140717442975432518741446853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93811628650288345827631235 140717442975432518741446853)
      ·
        refine ⟨26384520557893597264021285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140717442975432518741446853 26384520557893597264021285)
        ·
          refine ⟨4947097604605049487003991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26384520557893597264021285 4947097604605049487003991)
          ·
            refine ⟨7420646406907574230505987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4947097604605049487003991 7420646406907574230505987)
            ·
              refine ⟨11130969610361361345758981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7420646406907574230505987 11130969610361361345758981)
              ·
                refine ⟨2087056801942755252329809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11130969610361361345758981 2087056801942755252329809)
                ·
                  refine ⟨1565292601457066439247357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2087056801942755252329809 1565292601457066439247357)
                  ·
                    refine ⟨586984725546399914717759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565292601457066439247357 586984725546399914717759)
                    ·
                      rfl

theorem cell22_1714723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 3].length) (baseStart_1714723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714723 prefixEnd_1714723 := by exact prefixLift 1714723
  have htrace : WordTrace (prefixWord ++ tailWord_1714723) baseStart_1714723 baseEnd_1714723 := by
    simpa [prefixWord, tailWord_1714723, baseEnd_1714723] using wordTrace_append hprefix tailTrace_1714723
  have hstable : (prefixWord ++ tailWord_1714723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714723).length < 2 ^ (prefixWord ++ tailWord_1714723).sum := by decide
  have hdescent : baseEnd_1714723 < baseStart_1714723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714753 : List Nat := [1, 2, 5, 1, 1, 3, 3, 6]
def baseStart_1714753 : Nat := 118140960795 + 1714753 * 2 ^ 59
def prefixEnd_1714753 : Nat := 4983230072969 + 3 ^ 40 * 1714753 * 2
def baseEnd_1714753 : Nat := 65221666128832204051963

theorem tailTrace_1714753 : CollatzResearch.WordTrace tailWord_1714753 prefixEnd_1714753 65221666128832204051963 := by
  unfold tailWord_1714753
  simp only [CollatzResearch.WordTrace]
  refine ⟨62542179956750212342012913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41694786637833474894675275 62542179956750212342012913)
  ·
    refine ⟨46906634967562659256509685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62542179956750212342012913 46906634967562659256509685)
    ·
      refine ⟨4397497028208999305297783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46906634967562659256509685 4397497028208999305297783)
      ·
        refine ⟨6596245542313498957946675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4397497028208999305297783 6596245542313498957946675)
        ·
          refine ⟨9894368313470248436920013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6596245542313498957946675 9894368313470248436920013)
          ·
            refine ⟨3710388117551343163845005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9894368313470248436920013 3710388117551343163845005)
            ·
              refine ⟨1391395544081753686441877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3710388117551343163845005 1391395544081753686441877)
              ·
                refine ⟨65221666128832204051963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1391395544081753686441877 65221666128832204051963)
                ·
                  rfl

theorem cell22_1714753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 3, 6].length) (baseStart_1714753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714753 prefixEnd_1714753 := by exact prefixLift 1714753
  have htrace : WordTrace (prefixWord ++ tailWord_1714753) baseStart_1714753 baseEnd_1714753 := by
    simpa [prefixWord, tailWord_1714753, baseEnd_1714753] using wordTrace_append hprefix tailTrace_1714753
  have hstable : (prefixWord ++ tailWord_1714753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714753).length < 2 ^ (prefixWord ++ tailWord_1714753).sum := by decide
  have hdescent : baseEnd_1714753 < baseStart_1714753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714779 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 1, 13]
def baseStart_1714779 : Nat := 118140960795 + 1714779 * 2 ^ 59
def prefixEnd_1714779 : Nat := 4983230072969 + 3 ^ 40 * 1714779 * 2
def baseEnd_1714779 : Nat := 587003895490834435317587

theorem tailTrace_1714779 : CollatzResearch.WordTrace tailWord_1714779 prefixEnd_1714779 587003895490834435317587 := by
  unfold tailWord_1714779
  simp only [CollatzResearch.WordTrace]
  refine ⟨62543128254656018782459391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41695418836437345854972927 62543128254656018782459391)
  ·
    refine ⟨93814692381984028173689087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62543128254656018782459391 93814692381984028173689087)
    ·
      refine ⟨140722038572976042260533631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93814692381984028173689087 140722038572976042260533631)
      ·
        refine ⟨211083057859464063390800447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140722038572976042260533631 211083057859464063390800447)
        ·
          refine ⟨316624586789196095086200671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 211083057859464063390800447 316624586789196095086200671)
          ·
            refine ⟨474936880183794142629301007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 316624586789196095086200671 474936880183794142629301007)
            ·
              refine ⟨712405320275691213943951511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 474936880183794142629301007 712405320275691213943951511)
              ·
                refine ⟨1068607980413536820915927267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 712405320275691213943951511 1068607980413536820915927267)
                ·
                  refine ⟨1602911970620305231373890901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1068607980413536820915927267 1602911970620305231373890901)
                  ·
                    refine ⟨587003895490834435317587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 13 1602911970620305231373890901 587003895490834435317587)
                    ·
                      rfl

theorem cell22_1714779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 13].length) (baseStart_1714779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714779 prefixEnd_1714779 := by exact prefixLift 1714779
  have htrace : WordTrace (prefixWord ++ tailWord_1714779) baseStart_1714779 baseEnd_1714779 := by
    simpa [prefixWord, tailWord_1714779, baseEnd_1714779] using wordTrace_append hprefix tailTrace_1714779
  have hstable : (prefixWord ++ tailWord_1714779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714779).length < 2 ^ (prefixWord ++ tailWord_1714779).sum := by decide
  have hdescent : baseEnd_1714779 < baseStart_1714779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714785 : List Nat := [1, 2, 3, 1, 1, 4, 2, 4, 1, 3]
def baseStart_1714785 : Nat := 118140960795 + 1714785 * 2 ^ 59
def prefixEnd_1714785 : Nat := 4983230072969 + 3 ^ 40 * 1714785 * 2
def baseEnd_1714785 : Nat := 587005949413452419667569

theorem tailTrace_1714785 : CollatzResearch.WordTrace tailWord_1714785 prefixEnd_1714785 587005949413452419667569 := by
  unfold tailWord_1714785
  simp only [CollatzResearch.WordTrace]
  refine ⟨62543347092634281807177809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41695564728422854538118539 62543347092634281807177809)
  ·
    refine ⟨46907510319475711355383357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62543347092634281807177809 46907510319475711355383357)
    ·
      refine ⟨17590316369803391758268759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46907510319475711355383357 17590316369803391758268759)
      ·
        refine ⟨26385474554705087637403139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17590316369803391758268759 26385474554705087637403139)
        ·
          refine ⟨39578211832057631456104709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26385474554705087637403139 39578211832057631456104709)
          ·
            refine ⟨7420914718510805898019633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39578211832057631456104709 7420914718510805898019633)
            ·
              refine ⟨5565686038883104423514725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7420914718510805898019633 5565686038883104423514725)
              ·
                refine ⟨1043566132290582079409011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5565686038883104423514725 1043566132290582079409011)
                ·
                  refine ⟨1565349198435873119113517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043566132290582079409011 1565349198435873119113517)
                  ·
                    refine ⟨587005949413452419667569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565349198435873119113517 587005949413452419667569)
                    ·
                      rfl

theorem cell22_1714785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 4, 1, 3].length) (baseStart_1714785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714785 prefixEnd_1714785 := by exact prefixLift 1714785
  have htrace : WordTrace (prefixWord ++ tailWord_1714785) baseStart_1714785 baseEnd_1714785 := by
    simpa [prefixWord, tailWord_1714785, baseEnd_1714785] using wordTrace_append hprefix tailTrace_1714785
  have hstable : (prefixWord ++ tailWord_1714785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714785).length < 2 ^ (prefixWord ++ tailWord_1714785).sum := by decide
  have hdescent : baseEnd_1714785 < baseStart_1714785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714796 : List Nat := [2, 2, 1, 1, 3, 1, 4, 1, 2, 5]
def baseStart_1714796 : Nat := 118140960795 + 1714796 * 2 ^ 59
def prefixEnd_1714796 : Nat := 4983230072969 + 3 ^ 40 * 1714796 * 2
def baseEnd_1714796 : Nat := 587009714938252057642535

theorem tailTrace_1714796 : CollatzResearch.WordTrace tailWord_1714796 prefixEnd_1714796 587009714938252057642535 := by
  unfold tailWord_1714796
  simp only [CollatzResearch.WordTrace]
  refine ⟨31271874147797215342914121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41695832197062953790552161 31271874147797215342914121)
  ·
    refine ⟨23453905610847911507185591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31271874147797215342914121 23453905610847911507185591)
    ·
      refine ⟨35180858416271867260778387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23453905610847911507185591 35180858416271867260778387)
      ·
        refine ⟨52771287624407800891167581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35180858416271867260778387 52771287624407800891167581)
        ·
          refine ⟨19789232859152925334187843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52771287624407800891167581 19789232859152925334187843)
          ·
            refine ⟨29683849288729388001281765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19789232859152925334187843 29683849288729388001281765)
            ·
              refine ⟨5565721741636760250240331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29683849288729388001281765 5565721741636760250240331)
              ·
                refine ⟨8348582612455140375360497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5565721741636760250240331 8348582612455140375360497)
                ·
                  refine ⟨6261436959341355281520373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8348582612455140375360497 6261436959341355281520373)
                  ·
                    refine ⟨587009714938252057642535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6261436959341355281520373 587009714938252057642535)
                    ·
                      rfl

theorem cell22_1714796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 5].length) (baseStart_1714796 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714796 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714796 prefixEnd_1714796 := by exact prefixLift 1714796
  have htrace : WordTrace (prefixWord ++ tailWord_1714796) baseStart_1714796 baseEnd_1714796 := by
    simpa [prefixWord, tailWord_1714796, baseEnd_1714796] using wordTrace_append hprefix tailTrace_1714796
  have hstable : (prefixWord ++ tailWord_1714796).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714796).length < 2 ^ (prefixWord ++ tailWord_1714796).sum := by decide
  have hdescent : baseEnd_1714796 < baseStart_1714796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714862 : List Nat := [4, 1, 4, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1714862 : Nat := 118140960795 + 1714862 * 2 ^ 59
def prefixEnd_1714862 : Nat := 4983230072969 + 3 ^ 40 * 1714862 * 2
def baseEnd_1714862 : Nat := 587032308087049885492333

theorem tailTrace_1714862 : CollatzResearch.WordTrace tailWord_1714862 prefixEnd_1714862 587032308087049885492333 := by
  unfold tailWord_1714862
  simp only [CollatzResearch.WordTrace]
  refine ⟨7818269439169415494716355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41697437008903549305153893 7818269439169415494716355)
  ·
    refine ⟨11727404158754123242074533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7818269439169415494716355 11727404158754123242074533)
    ·
      refine ⟨2198888279766398107888975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11727404158754123242074533 2198888279766398107888975)
      ·
        refine ⟨3298332419649597161833463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2198888279766398107888975 3298332419649597161833463)
        ·
          refine ⟨4947498629474395742750195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3298332419649597161833463 4947498629474395742750195)
          ·
            refine ⟨7421247944211593614125293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4947498629474395742750195 7421247944211593614125293)
            ·
              refine ⟨2782967979079347605296985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7421247944211593614125293 2782967979079347605296985)
              ·
                refine ⟨2087225984309510703972739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2782967979079347605296985 2087225984309510703972739)
                ·
                  refine ⟨3130838976464266055959109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087225984309510703972739 3130838976464266055959109)
                  ·
                    refine ⟨587032308087049885492333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3130838976464266055959109 587032308087049885492333)
                    ·
                      rfl

theorem cell22_1714862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1714862 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714862 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714862 prefixEnd_1714862 := by exact prefixLift 1714862
  have htrace : WordTrace (prefixWord ++ tailWord_1714862) baseStart_1714862 baseEnd_1714862 := by
    simpa [prefixWord, tailWord_1714862, baseEnd_1714862] using wordTrace_append hprefix tailTrace_1714862
  have hstable : (prefixWord ++ tailWord_1714862).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714862).length < 2 ^ (prefixWord ++ tailWord_1714862).sum := by decide
  have hdescent : baseEnd_1714862 < baseStart_1714862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714892 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 2, 3]
def baseStart_1714892 : Nat := 118140960795 + 1714892 * 2 ^ 59
def prefixEnd_1714892 : Nat := 4983230072969 + 3 ^ 40 * 1714892 * 2
def baseEnd_1714892 : Nat := 587042577700139807242241

theorem tailTrace_1714892 : CollatzResearch.WordTrace tailWord_1714892 prefixEnd_1714892 587042577700139807242241 := by
  unfold tailWord_1714892
  simp only [CollatzResearch.WordTrace]
  refine ⟨31273624851623319540661465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41698166468831092720881953 31273624851623319540661465)
  ·
    refine ⟨23455218638717489655496099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31273624851623319540661465 23455218638717489655496099)
    ·
      refine ⟨35182827958076234483244149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23455218638717489655496099 35182827958076234483244149)
      ·
        refine ⟨3298390121069646982804139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35182827958076234483244149 3298390121069646982804139)
        ·
          refine ⟨4947585181604470474206209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3298390121069646982804139 4947585181604470474206209)
          ·
            refine ⟨3710688886203352855654657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4947585181604470474206209 3710688886203352855654657)
            ·
              refine ⟨2783016664652514641740993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3710688886203352855654657 2783016664652514641740993)
              ·
                refine ⟨2087262498489385981305745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2783016664652514641740993 2087262498489385981305745)
                ·
                  refine ⟨1565446873867039485979309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2087262498489385981305745 1565446873867039485979309)
                  ·
                    refine ⟨587042577700139807242241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565446873867039485979309 587042577700139807242241)
                    ·
                      rfl

theorem cell22_1714892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 2, 3].length) (baseStart_1714892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714892 prefixEnd_1714892 := by exact prefixLift 1714892
  have htrace : WordTrace (prefixWord ++ tailWord_1714892) baseStart_1714892 baseEnd_1714892 := by
    simpa [prefixWord, tailWord_1714892, baseEnd_1714892] using wordTrace_append hprefix tailTrace_1714892
  have hstable : (prefixWord ++ tailWord_1714892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714892).length < 2 ^ (prefixWord ++ tailWord_1714892).sum := by decide
  have hdescent : baseEnd_1714892 < baseStart_1714892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714931 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 3, 7]
def baseStart_1714931 : Nat := 118140960795 + 1714931 * 2 ^ 59
def prefixEnd_1714931 : Nat := 4983230072969 + 3 ^ 40 * 1714931 * 2
def baseEnd_1714931 : Nat := 587055928197156705517121

theorem tailTrace_1714931 : CollatzResearch.WordTrace tailWord_1714931 prefixEnd_1714931 587055928197156705517121 := by
  unfold tailWord_1714931
  simp only [CollatzResearch.WordTrace]
  refine ⟨62548672150105348741992647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41699114766736899161328431 62548672150105348741992647)
  ·
    refine ⟨93823008225158023112988971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62548672150105348741992647 93823008225158023112988971)
    ·
      refine ⟨140734512337737034669483457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93823008225158023112988971 140734512337737034669483457)
      ·
        refine ⟨105550884253302776002112593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140734512337737034669483457 105550884253302776002112593)
        ·
          refine ⟨79163163189977082001584445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105550884253302776002112593 79163163189977082001584445)
          ·
            refine ⟨29686186196241405750594167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79163163189977082001584445 29686186196241405750594167)
            ·
              refine ⟨44529279294362108625891251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29686186196241405750594167 44529279294362108625891251)
              ·
                refine ⟨66793918941543162938836877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44529279294362108625891251 66793918941543162938836877)
                ·
                  refine ⟨25047719603078686102063829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66793918941543162938836877 25047719603078686102063829)
                  ·
                    refine ⟨587055928197156705517121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25047719603078686102063829 587055928197156705517121)
                    ·
                      rfl

theorem cell22_1714931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 3, 7].length) (baseStart_1714931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714931 prefixEnd_1714931 := by exact prefixLift 1714931
  have htrace : WordTrace (prefixWord ++ tailWord_1714931) baseStart_1714931 baseEnd_1714931 := by
    simpa [prefixWord, tailWord_1714931, baseEnd_1714931] using wordTrace_append hprefix tailTrace_1714931
  have hstable : (prefixWord ++ tailWord_1714931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714931).length < 2 ^ (prefixWord ++ tailWord_1714931).sum := by decide
  have hdescent : baseEnd_1714931 < baseStart_1714931 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714948 : List Nat := [2, 3, 2, 2, 1, 1, 1, 1, 4, 5]
def baseStart_1714948 : Nat := 118140960795 + 1714948 * 2 ^ 59
def prefixEnd_1714948 : Nat := 4983230072969 + 3 ^ 40 * 1714948 * 2
def baseEnd_1714948 : Nat := 587061747644574327842069

theorem tailTrace_1714948 : CollatzResearch.WordTrace tailWord_1714948 prefixEnd_1714948 587061747644574327842069 := by
  unfold tailWord_1714948
  simp only [CollatzResearch.WordTrace]
  refine ⟨31274646095521880322680749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41699528127362507096907665 31274646095521880322680749)
  ·
    refine ⟨11727992285820705121005281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31274646095521880322680749 11727992285820705121005281)
    ·
      refine ⟨8795994214365528840753961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11727992285820705121005281 8795994214365528840753961)
      ·
        refine ⟨6596995660774146630565471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8795994214365528840753961 6596995660774146630565471)
        ·
          refine ⟨9895493491161219945848207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6596995660774146630565471 9895493491161219945848207)
          ·
            refine ⟨14843240236741829918772311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9895493491161219945848207 14843240236741829918772311)
            ·
              refine ⟨22264860355112744878158467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14843240236741829918772311 22264860355112744878158467)
              ·
                refine ⟨33397290532669117317237701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22264860355112744878158467 33397290532669117317237701)
                ·
                  refine ⟨6261991974875459496982069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33397290532669117317237701 6261991974875459496982069)
                  ·
                    refine ⟨587061747644574327842069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6261991974875459496982069 587061747644574327842069)
                    ·
                      rfl

theorem cell22_1714948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 1, 4, 5].length) (baseStart_1714948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714948 prefixEnd_1714948 := by exact prefixLift 1714948
  have htrace : WordTrace (prefixWord ++ tailWord_1714948) baseStart_1714948 baseEnd_1714948 := by
    simpa [prefixWord, tailWord_1714948, baseEnd_1714948] using wordTrace_append hprefix tailTrace_1714948
  have hstable : (prefixWord ++ tailWord_1714948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714948).length < 2 ^ (prefixWord ++ tailWord_1714948).sum := by decide
  have hdescent : baseEnd_1714948 < baseStart_1714948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714967 : List Nat := [1, 1, 3, 4, 3, 1, 3, 1, 5]
def baseStart_1714967 : Nat := 118140960795 + 1714967 * 2 ^ 59
def prefixEnd_1714967 : Nat := 4983230072969 + 3 ^ 40 * 1714967 * 2
def baseEnd_1714967 : Nat := 195689417244288203872337

theorem tailTrace_1714967 : CollatzResearch.WordTrace tailWord_1714967 prefixEnd_1714967 195689417244288203872337 := by
  unfold tailWord_1714967
  simp only [CollatzResearch.WordTrace]
  refine ⟨62549985177974926890303155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41699990118649951260202103 62549985177974926890303155)
  ·
    refine ⟨93824977766962390335454733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62549985177974926890303155 93824977766962390335454733)
    ·
      refine ⟨35184366662610896375795525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93824977766962390335454733 35184366662610896375795525)
      ·
        refine ⟨6597068749239543070461661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35184366662610896375795525 6597068749239543070461661)
        ·
          refine ⟨2473900780964828651423123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6597068749239543070461661 2473900780964828651423123)
          ·
            refine ⟨3710851171447242977134685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2473900780964828651423123 3710851171447242977134685)
            ·
              refine ⟨1391569189292716116425507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3710851171447242977134685 1391569189292716116425507)
              ·
                refine ⟨2087353783939074174638261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391569189292716116425507 2087353783939074174638261)
                ·
                  refine ⟨195689417244288203872337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2087353783939074174638261 195689417244288203872337)
                  ·
                    rfl

theorem cell22_1714967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 3, 1, 5].length) (baseStart_1714967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714967 prefixEnd_1714967 := by exact prefixLift 1714967
  have htrace : WordTrace (prefixWord ++ tailWord_1714967) baseStart_1714967 baseEnd_1714967 := by
    simpa [prefixWord, tailWord_1714967, baseEnd_1714967] using wordTrace_append hprefix tailTrace_1714967
  have hstable : (prefixWord ++ tailWord_1714967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714967).length < 2 ^ (prefixWord ++ tailWord_1714967).sum := by decide
  have hdescent : baseEnd_1714967 < baseStart_1714967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1714993 : List Nat := [1, 2, 2, 3, 2, 1, 2, 1, 3, 5]
def baseStart_1714993 : Nat := 118140960795 + 1714993 * 2 ^ 59
def prefixEnd_1714993 : Nat := 4983230072969 + 3 ^ 40 * 1714993 * 2
def baseEnd_1714993 : Nat := 587077152064209210466931

theorem tailTrace_1714993 : CollatzResearch.WordTrace tailWord_1714993 prefixEnd_1714993 587077152064209210466931 := by
  unfold tailWord_1714993
  simp only [CollatzResearch.WordTrace]
  refine ⟨62550933475880733330749633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41700622317253822220499755 62550933475880733330749633)
  ·
    refine ⟨46913200106910549998062225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62550933475880733330749633 46913200106910549998062225)
    ·
      refine ⟨35184900080182912498546669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46913200106910549998062225 35184900080182912498546669)
      ·
        refine ⟨13194337530068592186955001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35184900080182912498546669 13194337530068592186955001)
        ·
          refine ⟨9895753147551444140216251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13194337530068592186955001 9895753147551444140216251)
          ·
            refine ⟨14843629721327166210324377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9895753147551444140216251 14843629721327166210324377)
            ·
              refine ⟨11132722290995374657743283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14843629721327166210324377 11132722290995374657743283)
              ·
                refine ⟨16699083436493061986614925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11132722290995374657743283 16699083436493061986614925)
                ·
                  refine ⟨6262156288684898244980597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16699083436493061986614925 6262156288684898244980597)
                  ·
                    refine ⟨587077152064209210466931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6262156288684898244980597 587077152064209210466931)
                    ·
                      rfl

theorem cell22_1714993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 3, 5].length) (baseStart_1714993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1714993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1714993 prefixEnd_1714993 := by exact prefixLift 1714993
  have htrace : WordTrace (prefixWord ++ tailWord_1714993) baseStart_1714993 baseEnd_1714993 := by
    simpa [prefixWord, tailWord_1714993, baseEnd_1714993] using wordTrace_append hprefix tailTrace_1714993
  have hstable : (prefixWord ++ tailWord_1714993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1714993).length < 2 ^ (prefixWord ++ tailWord_1714993).sum := by decide
  have hdescent : baseEnd_1714993 < baseStart_1714993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1714993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715068 : List Nat := [2, 2, 2, 1, 1, 1, 1, 5, 7]
def baseStart_1715068 : Nat := 118140960795 + 1715068 * 2 ^ 59
def prefixEnd_1715068 : Nat := 4983230072969 + 3 ^ 40 * 1715068 * 2
def baseEnd_1715068 : Nat := 195700942032311338280567

theorem tailTrace_1715068 : CollatzResearch.WordTrace tailWord_1715068 prefixEnd_1715068 195700942032311338280567 := by
  unfold tailWord_1715068
  simp only [CollatzResearch.WordTrace]
  refine ⟨31276834475304510569864929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41702445967072680759819905 31276834475304510569864929)
  ·
    refine ⟨23457625856478382927398697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31276834475304510569864929 23457625856478382927398697)
    ·
      refine ⟨17593219392358787195549023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23457625856478382927398697 17593219392358787195549023)
      ·
        refine ⟨26389829088538180793323535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17593219392358787195549023 26389829088538180793323535)
        ·
          refine ⟨39584743632807271189985303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26389829088538180793323535 39584743632807271189985303)
          ·
            refine ⟨59377115449210906784977955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39584743632807271189985303 59377115449210906784977955)
            ·
              refine ⟨89065673173816360177466933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59377115449210906784977955 89065673173816360177466933)
              ·
                refine ⟨8349906860045283766637525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89065673173816360177466933 8349906860045283766637525)
                ·
                  refine ⟨195700942032311338280567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8349906860045283766637525 195700942032311338280567)
                  ·
                    rfl

theorem cell22_1715068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 5, 7].length) (baseStart_1715068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715068 prefixEnd_1715068 := by exact prefixLift 1715068
  have htrace : WordTrace (prefixWord ++ tailWord_1715068) baseStart_1715068 baseEnd_1715068 := by
    simpa [prefixWord, tailWord_1715068, baseEnd_1715068] using wordTrace_append hprefix tailTrace_1715068
  have hstable : (prefixWord ++ tailWord_1715068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715068).length < 2 ^ (prefixWord ++ tailWord_1715068).sum := by decide
  have hdescent : baseEnd_1715068 < baseStart_1715068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715083 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 1, 7]
def baseStart_1715083 : Nat := 118140960795 + 1715083 * 2 ^ 59
def prefixEnd_1715083 : Nat := 4983230072969 + 3 ^ 40 * 1715083 * 2
def baseEnd_1715083 : Nat := 587107960903478975716655

theorem tailTrace_1715083 : CollatzResearch.WordTrace tailWord_1715083 prefixEnd_1715083 587107960903478975716655 := by
  unfold tailWord_1715083
  simp only [CollatzResearch.WordTrace]
  refine ⟨62554216045554678701525903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41702810697036452467683935 62554216045554678701525903)
  ·
    refine ⟨93831324068332018052288855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62554216045554678701525903 93831324068332018052288855)
    ·
      refine ⟨140746986102498027078433283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93831324068332018052288855 140746986102498027078433283)
      ·
        refine ⟨211120479153747040617649925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140746986102498027078433283 211120479153747040617649925)
        ·
          refine ⟨39585089841327570115809361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211120479153747040617649925 39585089841327570115809361)
          ·
            refine ⟨29688817380995677586857021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39585089841327570115809361 29688817380995677586857021)
            ·
              refine ⟨11133306517873379095071383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29688817380995677586857021 11133306517873379095071383)
              ·
                refine ⟨16699959776810068642607075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11133306517873379095071383 16699959776810068642607075)
                ·
                  refine ⟨25049939665215102963910613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16699959776810068642607075 25049939665215102963910613)
                  ·
                    refine ⟨587107960903478975716655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25049939665215102963910613 587107960903478975716655)
                    ·
                      rfl

theorem cell22_1715083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 7].length) (baseStart_1715083 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715083 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715083 prefixEnd_1715083 := by exact prefixLift 1715083
  have htrace : WordTrace (prefixWord ++ tailWord_1715083) baseStart_1715083 baseEnd_1715083 := by
    simpa [prefixWord, tailWord_1715083, baseEnd_1715083] using wordTrace_append hprefix tailTrace_1715083
  have hstable : (prefixWord ++ tailWord_1715083).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715083).length < 2 ^ (prefixWord ++ tailWord_1715083).sum := by decide
  have hdescent : baseEnd_1715083 < baseStart_1715083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715106 : List Nat := [3, 3, 1, 2, 2, 2, 2, 3, 1, 3]
def baseStart_1715106 : Nat := 118140960795 + 1715106 * 2 ^ 59
def prefixEnd_1715106 : Nat := 4983230072969 + 3 ^ 40 * 1715106 * 2
def baseEnd_1715106 : Nat := 587115834273514582391585

theorem tailTrace_1715106 : CollatzResearch.WordTrace tailWord_1715106 prefixEnd_1715106 587115834273514582391585 := by
  unfold tailWord_1715106
  simp only [CollatzResearch.WordTrace]
  refine ⟨15638763731117838407403293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41703369949647569086408781 15638763731117838407403293)
  ·
    refine ⟨5864536399169189402776235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15638763731117838407403293 5864536399169189402776235)
    ·
      refine ⟨8796804598753784104164353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5864536399169189402776235 8796804598753784104164353)
      ·
        refine ⟨6597603449065338078123265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8796804598753784104164353 6597603449065338078123265)
        ·
          refine ⟨4948202586799003558592449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6597603449065338078123265 4948202586799003558592449)
          ·
            refine ⟨3711151940099252668944337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4948202586799003558592449 3711151940099252668944337)
            ·
              refine ⟨2783363955074439501708253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3711151940099252668944337 2783363955074439501708253)
              ·
                refine ⟨1043761483152914813140595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2783363955074439501708253 1043761483152914813140595)
                ·
                  refine ⟨1565642224729372219710893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043761483152914813140595 1565642224729372219710893)
                  ·
                    refine ⟨587115834273514582391585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565642224729372219710893 587115834273514582391585)
                    ·
                      rfl

theorem cell22_1715106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 3, 1, 3].length) (baseStart_1715106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715106 prefixEnd_1715106 := by exact prefixLift 1715106
  have htrace : WordTrace (prefixWord ++ tailWord_1715106) baseStart_1715106 baseEnd_1715106 := by
    simpa [prefixWord, tailWord_1715106, baseEnd_1715106] using wordTrace_append hprefix tailTrace_1715106
  have hstable : (prefixWord ++ tailWord_1715106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715106).length < 2 ^ (prefixWord ++ tailWord_1715106).sum := by decide
  have hdescent : baseEnd_1715106 < baseStart_1715106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715113 : List Nat := [1, 2, 1, 1, 1, 1, 5, 2, 8]
def baseStart_1715113 : Nat := 118140960795 + 1715113 * 2 ^ 59
def prefixEnd_1715113 : Nat := 4983230072969 + 3 ^ 40 * 1715113 * 2
def baseEnd_1715113 : Nat := 195706076838856299155521

theorem tailTrace_1715113 : CollatzResearch.WordTrace tailWord_1715113 prefixEnd_1715113 195706076838856299155521 := by
  unfold tailWord_1715113
  simp only [CollatzResearch.WordTrace]
  refine ⟨62555310235445993825117993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41703540156963995883411995 62555310235445993825117993)
  ·
    refine ⟨46916482676584495368838495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62555310235445993825117993 46916482676584495368838495)
    ·
      refine ⟨70374724014876743053257743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46916482676584495368838495 70374724014876743053257743)
      ·
        refine ⟨105562086022315114579886615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70374724014876743053257743 105562086022315114579886615)
        ·
          refine ⟨158343129033472671869829923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105562086022315114579886615 158343129033472671869829923)
          ·
            refine ⟨237514693550209007804744885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158343129033472671869829923 237514693550209007804744885)
            ·
              refine ⟨22267002520332094481694833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 237514693550209007804744885 22267002520332094481694833)
              ·
                refine ⟨16700251890249070861271125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22267002520332094481694833 16700251890249070861271125)
                ·
                  refine ⟨195706076838856299155521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16700251890249070861271125 195706076838856299155521)
                  ·
                    rfl

theorem cell22_1715113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 2, 8].length) (baseStart_1715113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715113 prefixEnd_1715113 := by exact prefixLift 1715113
  have htrace : WordTrace (prefixWord ++ tailWord_1715113) baseStart_1715113 baseEnd_1715113 := by
    simpa [prefixWord, tailWord_1715113, baseEnd_1715113] using wordTrace_append hprefix tailTrace_1715113
  have hstable : (prefixWord ++ tailWord_1715113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715113).length < 2 ^ (prefixWord ++ tailWord_1715113).sum := by decide
  have hdescent : baseEnd_1715113 < baseStart_1715113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715115 : List Nat := [1, 1, 1, 1, 2, 1, 1, 9, 1, 4]
def baseStart_1715115 : Nat := 118140960795 + 1715115 * 2 ^ 59
def prefixEnd_1715115 : Nat := 4983230072969 + 3 ^ 40 * 1715115 * 2
def baseEnd_1715115 : Nat := 587118915157441558916557

theorem tailTrace_1715115 : CollatzResearch.WordTrace tailWord_1715115 prefixEnd_1715115 587118915157441558916557 := by
  unfold tailWord_1715115
  simp only [CollatzResearch.WordTrace]
  refine ⟨62555383181438748166690799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41703588787625832111127199 62555383181438748166690799)
  ·
    refine ⟨93833074772158122250036199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62555383181438748166690799 93833074772158122250036199)
    ·
      refine ⟨140749612158237183375054299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93833074772158122250036199 140749612158237183375054299)
      ·
        refine ⟨211124418237355775062581449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140749612158237183375054299 211124418237355775062581449)
        ·
          refine ⟨158343313678016831296936087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211124418237355775062581449 158343313678016831296936087)
          ·
            refine ⟨237514970517025246945404131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158343313678016831296936087 237514970517025246945404131)
            ·
              refine ⟨356272455775537870418106197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 237514970517025246945404131 356272455775537870418106197)
              ·
                refine ⟨2087533920559792209481091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 356272455775537870418106197 2087533920559792209481091)
                ·
                  refine ⟨3131300880839688314221637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087533920559792209481091 3131300880839688314221637)
                  ·
                    refine ⟨587118915157441558916557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3131300880839688314221637 587118915157441558916557)
                    ·
                      rfl

theorem cell22_1715115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 9, 1, 4].length) (baseStart_1715115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715115 prefixEnd_1715115 := by exact prefixLift 1715115
  have htrace : WordTrace (prefixWord ++ tailWord_1715115) baseStart_1715115 baseEnd_1715115 := by
    simpa [prefixWord, tailWord_1715115, baseEnd_1715115] using wordTrace_append hprefix tailTrace_1715115
  have hstable : (prefixWord ++ tailWord_1715115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715115).length < 2 ^ (prefixWord ++ tailWord_1715115).sum := by decide
  have hdescent : baseEnd_1715115 < baseStart_1715115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715130 : List Nat := [3, 1, 1, 1, 2, 1, 6, 1, 6]
def baseStart_1715130 : Nat := 118140960795 + 1715130 * 2 ^ 59
def prefixEnd_1715130 : Nat := 4983230072969 + 3 ^ 40 * 1715130 * 2
def baseEnd_1715130 : Nat := 195708016654662173263837

theorem tailTrace_1715130 : CollatzResearch.WordTrace tailWord_1715130 prefixEnd_1715130 195708016654662173263837 := by
  unfold tailWord_1715130
  simp only [CollatzResearch.WordTrace]
  refine ⟨15638982569096101432121711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41703953517589603818991229 15638982569096101432121711)
  ·
    refine ⟨23458473853644152148182567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15638982569096101432121711 23458473853644152148182567)
    ·
      refine ⟨35187710780466228222273851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23458473853644152148182567 35187710780466228222273851)
      ·
        refine ⟨52781566170699342333410777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35187710780466228222273851 52781566170699342333410777)
        ·
          refine ⟨39586174628024506750058083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52781566170699342333410777 39586174628024506750058083)
          ·
            refine ⟨59379261942036760125087125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39586174628024506750058083 59379261942036760125087125)
            ·
              refine ⟨2783402903532973130863459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 59379261942036760125087125 2783402903532973130863459)
              ·
                refine ⟨4175104355299459696295189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2783402903532973130863459 4175104355299459696295189)
                ·
                  refine ⟨195708016654662173263837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4175104355299459696295189 195708016654662173263837)
                  ·
                    rfl

theorem cell22_1715130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 6, 1, 6].length) (baseStart_1715130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715130 prefixEnd_1715130 := by exact prefixLift 1715130
  have htrace : WordTrace (prefixWord ++ tailWord_1715130) baseStart_1715130 baseEnd_1715130 := by
    simpa [prefixWord, tailWord_1715130, baseEnd_1715130] using wordTrace_append hprefix tailTrace_1715130
  have hstable : (prefixWord ++ tailWord_1715130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715130).length < 2 ^ (prefixWord ++ tailWord_1715130).sum := by decide
  have hdescent : baseEnd_1715130 < baseStart_1715130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715145 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 8, 3]
def baseStart_1715145 : Nat := 118140960795 + 1715145 * 2 ^ 59
def prefixEnd_1715145 : Nat := 4983230072969 + 3 ^ 40 * 1715145 * 2
def baseEnd_1715145 : Nat := 587129184770531480666465

theorem tailTrace_1715145 : CollatzResearch.WordTrace tailWord_1715145 prefixEnd_1715145 587129184770531480666465 := by
  unfold tailWord_1715145
  simp only [CollatzResearch.WordTrace]
  refine ⟨62556477371330063290282889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41704318247553375526855259 62556477371330063290282889)
  ·
    refine ⟨46917358028497547467712167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62556477371330063290282889 46917358028497547467712167)
    ·
      refine ⟨70376037042746321201568251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46917358028497547467712167 70376037042746321201568251)
      ·
        refine ⟨105564055564119481802352377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70376037042746321201568251 105564055564119481802352377)
        ·
          refine ⟨79173041673089611351764283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105564055564119481802352377 79173041673089611351764283)
          ·
            refine ⟨118759562509634417027646425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79173041673089611351764283 118759562509634417027646425)
            ·
              refine ⟨89069671882225812770734819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118759562509634417027646425 89069671882225812770734819)
              ·
                refine ⟨133604507823338719156102229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89069671882225812770734819 133604507823338719156102229)
                ·
                  refine ⟨1565677826054750615110573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 133604507823338719156102229 1565677826054750615110573)
                  ·
                    refine ⟨587129184770531480666465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565677826054750615110573 587129184770531480666465)
                    ·
                      rfl

theorem cell22_1715145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 8, 3].length) (baseStart_1715145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715145 prefixEnd_1715145 := by exact prefixLift 1715145
  have htrace : WordTrace (prefixWord ++ tailWord_1715145) baseStart_1715145 baseEnd_1715145 := by
    simpa [prefixWord, tailWord_1715145, baseEnd_1715145] using wordTrace_append hprefix tailTrace_1715145
  have hstable : (prefixWord ++ tailWord_1715145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715145).length < 2 ^ (prefixWord ++ tailWord_1715145).sum := by decide
  have hdescent : baseEnd_1715145 < baseStart_1715145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715160 : List Nat := [2, 1, 2, 2, 2, 3, 2, 1, 1, 6]
def baseStart_1715160 : Nat := 118140960795 + 1715160 * 2 ^ 59
def prefixEnd_1715160 : Nat := 4983230072969 + 3 ^ 40 * 1715160 * 2
def baseEnd_1715160 : Nat := 587134319577076441541419

theorem tailTrace_1715160 : CollatzResearch.WordTrace tailWord_1715160 prefixEnd_1715160 587134319577076441541419 := by
  unfold tailWord_1715160
  simp only [CollatzResearch.WordTrace]
  refine ⟨31278512233137860426039467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41704682977517147234719289 31278512233137860426039467)
  ·
    refine ⟨46917768349706790639059201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31278512233137860426039467 46917768349706790639059201)
    ·
      refine ⟨35188326262280092979294401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46917768349706790639059201 35188326262280092979294401)
      ·
        refine ⟨26391244696710069734470801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35188326262280092979294401 26391244696710069734470801)
        ·
          refine ⟨19793433522532552300853101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26391244696710069734470801 19793433522532552300853101)
          ·
            refine ⟨7422537570949707112819913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19793433522532552300853101 7422537570949707112819913)
            ·
              refine ⟨5566903178212280334614935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7422537570949707112819913 5566903178212280334614935)
              ·
                refine ⟨8350354767318420501922403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5566903178212280334614935 8350354767318420501922403)
                ·
                  refine ⟨12525532150977630752883605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8350354767318420501922403 12525532150977630752883605)
                  ·
                    refine ⟨587134319577076441541419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12525532150977630752883605 587134319577076441541419)
                    ·
                      rfl

theorem cell22_1715160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_1715160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715160 prefixEnd_1715160 := by exact prefixLift 1715160
  have htrace : WordTrace (prefixWord ++ tailWord_1715160) baseStart_1715160 baseEnd_1715160 := by
    simpa [prefixWord, tailWord_1715160, baseEnd_1715160] using wordTrace_append hprefix tailTrace_1715160
  have hstable : (prefixWord ++ tailWord_1715160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715160).length < 2 ^ (prefixWord ++ tailWord_1715160).sum := by decide
  have hdescent : baseEnd_1715160 < baseStart_1715160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715162 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 4, 3]
def baseStart_1715162 : Nat := 118140960795 + 1715162 * 2 ^ 59
def prefixEnd_1715162 : Nat := 4983230072969 + 3 ^ 40 * 1715162 * 2
def baseEnd_1715162 : Nat := 587135004217949102991413

theorem tailTrace_1715162 : CollatzResearch.WordTrace tailWord_1715162 prefixEnd_1715162 587135004217949102991413 := by
  unfold tailWord_1715162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15639274353067118798412935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41704731608178983462434493 15639274353067118798412935)
  ·
    refine ⟨23458911529600678197619403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15639274353067118798412935 23458911529600678197619403)
    ·
      refine ⟨35188367294401017296429105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23458911529600678197619403 35188367294401017296429105)
      ·
        refine ⟨26391275470800762972321829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35188367294401017296429105 26391275470800762972321829)
        ·
          refine ⟨4948364150775143057310343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26391275470800762972321829 4948364150775143057310343)
          ·
            refine ⟨7422546226162714585965515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948364150775143057310343 7422546226162714585965515)
            ·
              refine ⟨11133819339244071878948273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7422546226162714585965515 11133819339244071878948273)
              ·
                refine ⟨8350364504433053909211205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11133819339244071878948273 8350364504433053909211205)
                ·
                  refine ⟨1565693344581197607977101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8350364504433053909211205 1565693344581197607977101)
                  ·
                    refine ⟨587135004217949102991413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565693344581197607977101 587135004217949102991413)
                    ·
                      rfl

theorem cell22_1715162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_1715162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715162 prefixEnd_1715162 := by exact prefixLift 1715162
  have htrace : WordTrace (prefixWord ++ tailWord_1715162) baseStart_1715162 baseEnd_1715162 := by
    simpa [prefixWord, tailWord_1715162, baseEnd_1715162] using wordTrace_append hprefix tailTrace_1715162
  have hstable : (prefixWord ++ tailWord_1715162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715162).length < 2 ^ (prefixWord ++ tailWord_1715162).sum := by decide
  have hdescent : baseEnd_1715162 < baseStart_1715162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715175 : List Nat := [1, 1, 5, 2, 2, 1, 10]
def baseStart_1715175 : Nat := 118140960795 + 1715175 * 2 ^ 59
def prefixEnd_1715175 : Nat := 4983230072969 + 3 ^ 40 * 1715175 * 2
def baseEnd_1715175 : Nat := 21745905717911903793199

theorem tailTrace_1715175 : CollatzResearch.WordTrace tailWord_1715175 prefixEnd_1715175 21745905717911903793199 := by
  unfold tailWord_1715175
  simp only [CollatzResearch.WordTrace]
  refine ⟨62557571561221378413874979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41705047707480918942583319 62557571561221378413874979)
  ·
    refine ⟨93836357341832067620812469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62557571561221378413874979 93836357341832067620812469)
    ·
      refine ⟨8797158500796756339451169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93836357341832067620812469 8797158500796756339451169)
      ·
        refine ⟨6597868875597567254588377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8797158500796756339451169 6597868875597567254588377)
        ·
          refine ⟨4948401656698175440941283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6597868875597567254588377 4948401656698175440941283)
          ·
            refine ⟨7422602485047263161411925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4948401656698175440941283 7422602485047263161411925)
            ·
              refine ⟨21745905717911903793199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7422602485047263161411925 21745905717911903793199)
              ·
                rfl

theorem cell22_1715175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 10].length) (baseStart_1715175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715175 prefixEnd_1715175 := by exact prefixLift 1715175
  have htrace : WordTrace (prefixWord ++ tailWord_1715175) baseStart_1715175 baseEnd_1715175 := by
    simpa [prefixWord, tailWord_1715175, baseEnd_1715175] using wordTrace_append hprefix tailTrace_1715175
  have hstable : (prefixWord ++ tailWord_1715175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715175).length < 2 ^ (prefixWord ++ tailWord_1715175).sum := by decide
  have hdescent : baseEnd_1715175 < baseStart_1715175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715196 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 2, 3]
def baseStart_1715196 : Nat := 118140960795 + 1715196 * 2 ^ 59
def prefixEnd_1715196 : Nat := 4983230072969 + 3 ^ 40 * 1715196 * 2
def baseEnd_1715196 : Nat := 587146643112784347641309

theorem tailTrace_1715196 : CollatzResearch.WordTrace tailWord_1715196 prefixEnd_1715196 587146643112784347641309 := by
  unfold tailWord_1715196
  simp only [CollatzResearch.WordTrace]
  refine ⟨31279168747072649500194721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41705558329430199333592961 31279168747072649500194721)
  ·
    refine ⟨23459376560304487125146041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31279168747072649500194721 23459376560304487125146041)
    ·
      refine ⟨17594532420228365343859531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23459376560304487125146041 17594532420228365343859531)
      ·
        refine ⟨26391798630342548015789297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17594532420228365343859531 26391798630342548015789297)
        ·
          refine ⟨19793848972756911011841973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26391798630342548015789297 19793848972756911011841973)
          ·
            refine ⟨1855673341195960407360185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19793848972756911011841973 1855673341195960407360185)
            ·
              refine ⟨1391755005896970305520139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1855673341195960407360185 1391755005896970305520139)
              ·
                refine ⟨2087632508845455458280209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1391755005896970305520139 2087632508845455458280209)
                ·
                  refine ⟨1565724381634091593710157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2087632508845455458280209 1565724381634091593710157)
                  ·
                    refine ⟨587146643112784347641309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565724381634091593710157 587146643112784347641309)
                    ·
                      rfl

theorem cell22_1715196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 2, 3].length) (baseStart_1715196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715196 prefixEnd_1715196 := by exact prefixLift 1715196
  have htrace : WordTrace (prefixWord ++ tailWord_1715196) baseStart_1715196 baseEnd_1715196 := by
    simpa [prefixWord, tailWord_1715196, baseEnd_1715196] using wordTrace_append hprefix tailTrace_1715196
  have hstable : (prefixWord ++ tailWord_1715196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715196).length < 2 ^ (prefixWord ++ tailWord_1715196).sum := by decide
  have hdescent : baseEnd_1715196 < baseStart_1715196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715207 : List Nat := [1, 1, 4, 3, 1, 1, 2, 1, 5, 3]
def baseStart_1715207 : Nat := 118140960795 + 1715207 * 2 ^ 59
def prefixEnd_1715207 : Nat := 4983230072969 + 3 ^ 40 * 1715207 * 2
def baseEnd_1715207 : Nat := 587150408637583985616275

theorem tailTrace_1715207 : CollatzResearch.WordTrace tailWord_1715207 prefixEnd_1715207 587150408637583985616275 := by
  unfold tailWord_1715207
  simp only [CollatzResearch.WordTrace]
  refine ⟨62558738697105447879039875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41705825798070298586026583 62558738697105447879039875)
  ·
    refine ⟨93838108045658171818559813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62558738697105447879039875 93838108045658171818559813)
    ·
      refine ⟨17594645258560907215979965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93838108045658171818559813 17594645258560907215979965)
      ·
        refine ⟨6597991971960340205992487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17594645258560907215979965 6597991971960340205992487)
        ·
          refine ⟨9896987957940510308988731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6597991971960340205992487 9896987957940510308988731)
          ·
            refine ⟨14845481936910765463483097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9896987957940510308988731 14845481936910765463483097)
            ·
              refine ⟨11134111452683074097612323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14845481936910765463483097 11134111452683074097612323)
              ·
                refine ⟨16701167179024611146418485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11134111452683074097612323 16701167179024611146418485)
                ·
                  refine ⟨1565734423033557294976733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16701167179024611146418485 1565734423033557294976733)
                  ·
                    refine ⟨587150408637583985616275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565734423033557294976733 587150408637583985616275)
                    ·
                      rfl

theorem cell22_1715207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_1715207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715207 prefixEnd_1715207 := by exact prefixLift 1715207
  have htrace : WordTrace (prefixWord ++ tailWord_1715207) baseStart_1715207 baseEnd_1715207 := by
    simpa [prefixWord, tailWord_1715207, baseEnd_1715207] using wordTrace_append hprefix tailTrace_1715207
  have hstable : (prefixWord ++ tailWord_1715207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715207).length < 2 ^ (prefixWord ++ tailWord_1715207).sum := by decide
  have hdescent : baseEnd_1715207 < baseStart_1715207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715237 : List Nat := [1, 3, 1, 2, 2, 2, 4, 2, 5]
def baseStart_1715237 : Nat := 118140960795 + 1715237 * 2 ^ 59
def prefixEnd_1715237 : Nat := 4983230072969 + 3 ^ 40 * 1715237 * 2
def baseEnd_1715237 : Nat := 195720226083557969122061

theorem tailTrace_1715237 : CollatzResearch.WordTrace tailWord_1715237 prefixEnd_1715237 195720226083557969122061 := by
  unfold tailWord_1715237
  simp only [CollatzResearch.WordTrace]
  refine ⟨62559832886996763002631965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41706555257997842001754643 62559832886996763002631965)
  ·
    refine ⟨23459937332623786125986987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62559832886996763002631965 23459937332623786125986987)
    ·
      refine ⟨35189905998935679188980481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23459937332623786125986987 35189905998935679188980481)
      ·
        refine ⟨26392429499201759391735361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35189905998935679188980481 26392429499201759391735361)
        ·
          refine ⟨19794322124401319543801521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26392429499201759391735361 19794322124401319543801521)
          ·
            refine ⟨14845741593300989657851141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19794322124401319543801521 14845741593300989657851141)
            ·
              refine ⟨2783576548743935560847089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14845741593300989657851141 2783576548743935560847089)
              ·
                refine ⟨2087682411557951670635317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2783576548743935560847089 2087682411557951670635317)
                ·
                  refine ⟨195720226083557969122061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2087682411557951670635317 195720226083557969122061)
                  ·
                    rfl

theorem cell22_1715237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 4, 2, 5].length) (baseStart_1715237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715237 prefixEnd_1715237 := by exact prefixLift 1715237
  have htrace : WordTrace (prefixWord ++ tailWord_1715237) baseStart_1715237 baseEnd_1715237 := by
    simpa [prefixWord, tailWord_1715237, baseEnd_1715237] using wordTrace_append hprefix tailTrace_1715237
  have hstable : (prefixWord ++ tailWord_1715237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715237).length < 2 ^ (prefixWord ++ tailWord_1715237).sum := by decide
  have hdescent : baseEnd_1715237 < baseStart_1715237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715254 : List Nat := [5, 1, 2, 1, 1, 2, 2, 3, 5]
def baseStart_1715254 : Nat := 118140960795 + 1715254 * 2 ^ 59
def prefixEnd_1715254 : Nat := 4983230072969 + 3 ^ 40 * 1715254 * 2
def baseEnd_1715254 : Nat := 195722165899363843230377

theorem tailTrace_1715254 : CollatzResearch.WordTrace tailWord_1715254 prefixEnd_1715254 195722165899363843230377 := by
  unfold tailWord_1715254
  simp only [CollatzResearch.WordTrace]
  refine ⟨3910028307995948431625051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41706968618623449937333877 3910028307995948431625051)
  ·
    refine ⟨5865042461993922647437577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3910028307995948431625051 5865042461993922647437577)
    ·
      refine ⟨4398781846495441985578183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5865042461993922647437577 4398781846495441985578183)
      ·
        refine ⟨6598172769743162978367275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4398781846495441985578183 6598172769743162978367275)
        ·
          refine ⟨9897259154614744467550913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6598172769743162978367275 9897259154614744467550913)
          ·
            refine ⟨7422944365961058350663185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9897259154614744467550913 7422944365961058350663185)
            ·
              refine ⟨5567208274470793762997389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7422944365961058350663185 5567208274470793762997389)
              ·
                refine ⟨2087703102926547661124021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5567208274470793762997389 2087703102926547661124021)
                ·
                  refine ⟨195722165899363843230377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2087703102926547661124021 195722165899363843230377)
                  ·
                    rfl

theorem cell22_1715254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_1715254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715254 prefixEnd_1715254 := by exact prefixLift 1715254
  have htrace : WordTrace (prefixWord ++ tailWord_1715254) baseStart_1715254 baseEnd_1715254 := by
    simpa [prefixWord, tailWord_1715254, baseEnd_1715254] using wordTrace_append hprefix tailTrace_1715254
  have hstable : (prefixWord ++ tailWord_1715254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715254).length < 2 ^ (prefixWord ++ tailWord_1715254).sum := by decide
  have hdescent : baseEnd_1715254 < baseStart_1715254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715267 : List Nat := [1, 1, 1, 3, 1, 2, 4, 4, 1, 4]
def baseStart_1715267 : Nat := 118140960795 + 1715267 * 2 ^ 59
def prefixEnd_1715267 : Nat := 4983230072969 + 3 ^ 40 * 1715267 * 2
def baseEnd_1715267 : Nat := 587170947863763829116091

theorem tailTrace_1715267 : CollatzResearch.WordTrace tailWord_1715267 prefixEnd_1715267 587170947863763829116091 := by
  unfold tailWord_1715267
  simp only [CollatzResearch.WordTrace]
  refine ⟨62560927076888078126224055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41707284717925385417482703 62560927076888078126224055)
  ·
    refine ⟨93841390615332117189336083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62560927076888078126224055 93841390615332117189336083)
    ·
      refine ⟨140762085922998175784004125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93841390615332117189336083 140762085922998175784004125)
      ·
        refine ⟨52785782221124315919001547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140762085922998175784004125 52785782221124315919001547)
        ·
          refine ⟨79178673331686473878502321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52785782221124315919001547 79178673331686473878502321)
          ·
            refine ⟨59384004998764855408876741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79178673331686473878502321 59384004998764855408876741)
            ·
              refine ⟨11134500937268410389164389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59384004998764855408876741 11134500937268410389164389)
              ·
                refine ⟨2087718925737826947968323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11134500937268410389164389 2087718925737826947968323)
                ·
                  refine ⟨3131578388606740421952485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2087718925737826947968323 3131578388606740421952485)
                  ·
                    refine ⟨587170947863763829116091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3131578388606740421952485 587170947863763829116091)
                    ·
                      rfl

theorem cell22_1715267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 4, 4, 1, 4].length) (baseStart_1715267 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715267 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715267 prefixEnd_1715267 := by exact prefixLift 1715267
  have htrace : WordTrace (prefixWord ++ tailWord_1715267) baseStart_1715267 baseEnd_1715267 := by
    simpa [prefixWord, tailWord_1715267, baseEnd_1715267] using wordTrace_append hprefix tailTrace_1715267
  have hstable : (prefixWord ++ tailWord_1715267).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715267).length < 2 ^ (prefixWord ++ tailWord_1715267).sum := by decide
  have hdescent : baseEnd_1715267 < baseStart_1715267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715333 : List Nat := [1, 3, 1, 1, 7, 1, 1, 3, 4]
def baseStart_1715333 : Nat := 118140960795 + 1715333 * 2 ^ 59
def prefixEnd_1715333 : Nat := 4983230072969 + 3 ^ 40 * 1715333 * 2
def baseEnd_1715333 : Nat := 195731180337520552321963

theorem tailTrace_1715333 : CollatzResearch.WordTrace tailWord_1715333 prefixEnd_1715333 195731180337520552321963 := by
  unfold tailWord_1715333
  simp only [CollatzResearch.WordTrace]
  refine ⟨62563334294648971398126653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41708889529765980932084435 62563334294648971398126653)
  ·
    refine ⟨23461250360493364274297495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62563334294648971398126653 23461250360493364274297495)
    ·
      refine ⟨35191875540740046411446243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23461250360493364274297495 35191875540740046411446243)
      ·
        refine ⟨52787813311110069617169365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35191875540740046411446243 52787813311110069617169365)
        ·
          refine ⟨1237214374479142256652407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 52787813311110069617169365 1237214374479142256652407)
          ·
            refine ⟨1855821561718713384978611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237214374479142256652407 1855821561718713384978611)
            ·
              refine ⟨2783732342578070077467917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1855821561718713384978611 2783732342578070077467917)
              ·
                refine ⟨1043899628466776279050469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2783732342578070077467917 1043899628466776279050469)
                ·
                  refine ⟨195731180337520552321963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1043899628466776279050469 195731180337520552321963)
                  ·
                    rfl

theorem cell22_1715333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 7, 1, 1, 3, 4].length) (baseStart_1715333 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715333 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715333 prefixEnd_1715333 := by exact prefixLift 1715333
  have htrace : WordTrace (prefixWord ++ tailWord_1715333) baseStart_1715333 baseEnd_1715333 := by
    simpa [prefixWord, tailWord_1715333, baseEnd_1715333] using wordTrace_append hprefix tailTrace_1715333
  have hstable : (prefixWord ++ tailWord_1715333).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715333).length < 2 ^ (prefixWord ++ tailWord_1715333).sum := by decide
  have hdescent : baseEnd_1715333 < baseStart_1715333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715357 : List Nat := [1, 4, 2, 1, 1, 2, 2, 1, 2, 6]
def baseStart_1715357 : Nat := 118140960795 + 1715357 * 2 ^ 59
def prefixEnd_1715357 : Nat := 4983230072969 + 3 ^ 40 * 1715357 * 2
def baseEnd_1715357 : Nat := 587201756703033594365815

theorem tailTrace_1715357 : CollatzResearch.WordTrace tailWord_1715357 prefixEnd_1715357 587201756703033594365815 := by
  unfold tailWord_1715357
  simp only [CollatzResearch.WordTrace]
  refine ⟨62564209646562023497000325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41709473097708015664666883 62564209646562023497000325)
  ·
    refine ⟨11730789308730379405687561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62564209646562023497000325 11730789308730379405687561)
    ·
      refine ⟨8798091981547784554265671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11730789308730379405687561 8798091981547784554265671)
      ·
        refine ⟨13197137972321676831398507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8798091981547784554265671 13197137972321676831398507)
        ·
          refine ⟨19795706958482515247097761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13197137972321676831398507 19795706958482515247097761)
          ·
            refine ⟨14846780218861886435323321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19795706958482515247097761 14846780218861886435323321)
            ·
              refine ⟨11135085164146414826492491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14846780218861886435323321 11135085164146414826492491)
              ·
                refine ⟨16702627746219622239738737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11135085164146414826492491 16702627746219622239738737)
                ·
                  refine ⟨12526970809664716679804053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16702627746219622239738737 12526970809664716679804053)
                  ·
                    refine ⟨587201756703033594365815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12526970809664716679804053 587201756703033594365815)
                    ·
                      rfl

theorem cell22_1715357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_1715357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715357 prefixEnd_1715357 := by exact prefixLift 1715357
  have htrace : WordTrace (prefixWord ++ tailWord_1715357) baseStart_1715357 baseEnd_1715357 := by
    simpa [prefixWord, tailWord_1715357, baseEnd_1715357] using wordTrace_append hprefix tailTrace_1715357
  have hstable : (prefixWord ++ tailWord_1715357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715357).length < 2 ^ (prefixWord ++ tailWord_1715357).sum := by decide
  have hdescent : baseEnd_1715357 < baseStart_1715357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715406 : List Nat := [4, 1, 1, 1, 5, 1, 2, 2, 5]
def baseStart_1715406 : Nat := 118140960795 + 1715406 * 2 ^ 59
def prefixEnd_1715406 : Nat := 4983230072969 + 3 ^ 40 * 1715406 * 2
def baseEnd_1715406 : Nat := 195739510134804599963555

theorem tailTrace_1715406 : CollatzResearch.WordTrace tailWord_1715406 prefixEnd_1715406 195739510134804599963555 := by
  unfold tailWord_1715406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7820749602923063108191759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41710664548923003243689381 7820749602923063108191759)
  ·
    refine ⟨11731124404384594662287639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7820749602923063108191759 11731124404384594662287639)
    ·
      refine ⟨17596686606576891993431459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11731124404384594662287639 17596686606576891993431459)
      ·
        refine ⟨26395029909865337990147189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17596686606576891993431459 26395029909865337990147189)
        ·
          refine ⟨2474534054049875436576299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26395029909865337990147189 2474534054049875436576299)
          ·
            refine ⟨3711801081074813154864449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474534054049875436576299 3711801081074813154864449)
            ·
              refine ⟨2783850810806109866148337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3711801081074813154864449 2783850810806109866148337)
              ·
                refine ⟨2087888108104582399611253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2783850810806109866148337 2087888108104582399611253)
                ·
                  refine ⟨195739510134804599963555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2087888108104582399611253 195739510134804599963555)
                  ·
                    rfl

theorem cell22_1715406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 2, 2, 5].length) (baseStart_1715406 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715406 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715406 prefixEnd_1715406 := by exact prefixLift 1715406
  have htrace : WordTrace (prefixWord ++ tailWord_1715406) baseStart_1715406 baseEnd_1715406 := by
    simpa [prefixWord, tailWord_1715406, baseEnd_1715406] using wordTrace_append hprefix tailTrace_1715406
  have hstable : (prefixWord ++ tailWord_1715406).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715406).length < 2 ^ (prefixWord ++ tailWord_1715406).sum := by decide
  have hdescent : baseEnd_1715406 < baseStart_1715406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715417 : List Nat := [1, 2, 1, 2, 3, 1, 1, 5, 6]
def baseStart_1715417 : Nat := 118140960795 + 1715417 * 2 ^ 59
def prefixEnd_1715417 : Nat := 4983230072969 + 3 ^ 40 * 1715417 * 2
def baseEnd_1715417 : Nat := 195740765309737812621877

theorem tailTrace_1715417 : CollatzResearch.WordTrace tailWord_1715417 prefixEnd_1715417 195740765309737812621877 := by
  unfold tailWord_1715417
  simp only [CollatzResearch.WordTrace]
  refine ⟨62566398026344653744184505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41710932017563102496123003 62566398026344653744184505)
  ·
    refine ⟨46924798519758490308138379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62566398026344653744184505 46924798519758490308138379)
    ·
      refine ⟨70387197779637735462207569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46924798519758490308138379 70387197779637735462207569)
      ·
        refine ⟨52790398334728301596655677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70387197779637735462207569 52790398334728301596655677)
        ·
          refine ⟨19796399375523113098745879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52790398334728301596655677 19796399375523113098745879)
          ·
            refine ⟨29694599063284669648118819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19796399375523113098745879 29694599063284669648118819)
            ·
              refine ⟨44541898594927004472178229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29694599063284669648118819 44541898594927004472178229)
              ·
                refine ⟨4175802993274406669266709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44541898594927004472178229 4175802993274406669266709)
                ·
                  refine ⟨195740765309737812621877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4175802993274406669266709 195740765309737812621877)
                  ·
                    rfl

theorem cell22_1715417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 5, 6].length) (baseStart_1715417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715417 prefixEnd_1715417 := by exact prefixLift 1715417
  have htrace : WordTrace (prefixWord ++ tailWord_1715417) baseStart_1715417 baseEnd_1715417 := by
    simpa [prefixWord, tailWord_1715417, baseEnd_1715417] using wordTrace_append hprefix tailTrace_1715417
  have hstable : (prefixWord ++ tailWord_1715417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715417).length < 2 ^ (prefixWord ++ tailWord_1715417).sum := by decide
  have hdescent : baseEnd_1715417 < baseStart_1715417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715421 : List Nat := [1, 4, 3, 2, 2, 1, 1, 1, 2, 5]
def baseStart_1715421 : Nat := 118140960795 + 1715421 * 2 ^ 59
def prefixEnd_1715421 : Nat := 4983230072969 + 3 ^ 40 * 1715421 * 2
def baseEnd_1715421 : Nat := 587223665210958760765619

theorem tailTrace_1715421 : CollatzResearch.WordTrace tailWord_1715421 prefixEnd_1715421 587223665210958760765619 := by
  unfold tailWord_1715421
  simp only [CollatzResearch.WordTrace]
  refine ⟨62566543918330162427330117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41711029278886774951553411 62566543918330162427330117)
  ·
    refine ⟨11731226984686905455124397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62566543918330162427330117 11731226984686905455124397)
    ·
      refine ⟨4399210119257589545671649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11731226984686905455124397 4399210119257589545671649)
      ·
        refine ⟨3299407589443192159253737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4399210119257589545671649 3299407589443192159253737)
        ·
          refine ⟨2474555692082394119440303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3299407589443192159253737 2474555692082394119440303)
          ·
            refine ⟨3711833538123591179160455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474555692082394119440303 3711833538123591179160455)
            ·
              refine ⟨5567750307185386768740683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711833538123591179160455 5567750307185386768740683)
              ·
                refine ⟨8351625460778080153111025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5567750307185386768740683 8351625460778080153111025)
                ·
                  refine ⟨6263719095583560114833269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8351625460778080153111025 6263719095583560114833269)
                  ·
                    refine ⟨587223665210958760765619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6263719095583560114833269 587223665210958760765619)
                    ·
                      rfl

theorem cell22_1715421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 1, 1, 2, 5].length) (baseStart_1715421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715421 prefixEnd_1715421 := by exact prefixLift 1715421
  have htrace : WordTrace (prefixWord ++ tailWord_1715421) baseStart_1715421 baseEnd_1715421 := by
    simpa [prefixWord, tailWord_1715421, baseEnd_1715421] using wordTrace_append hprefix tailTrace_1715421
  have hstable : (prefixWord ++ tailWord_1715421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715421).length < 2 ^ (prefixWord ++ tailWord_1715421).sum := by decide
  have hdescent : baseEnd_1715421 < baseStart_1715421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715434 : List Nat := [3, 1, 3, 1, 1, 4, 1, 2, 6]
def baseStart_1715434 : Nat := 118140960795 + 1715434 * 2 ^ 59
def prefixEnd_1715434 : Nat := 4983230072969 + 3 ^ 40 * 1715434 * 2
def baseEnd_1715434 : Nat := 195742705125543686730193

theorem tailTrace_1715434 : CollatzResearch.WordTrace tailWord_1715434 prefixEnd_1715434 195742705125543686730193 := by
  unfold tailWord_1715434
  simp only [CollatzResearch.WordTrace]
  refine ⟨15641754516820766411888339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41711345378188710431702237 15641754516820766411888339)
  ·
    refine ⟨23462631775231149617832509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15641754516820766411888339 23462631775231149617832509)
    ·
      refine ⟨8798486915711681106687191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23462631775231149617832509 8798486915711681106687191)
      ·
        refine ⟨13197730373567521660030787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8798486915711681106687191 13197730373567521660030787)
        ·
          refine ⟨19796595560351282490046181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13197730373567521660030787 19796595560351282490046181)
          ·
            refine ⟨3711861667565865466883659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19796595560351282490046181 3711861667565865466883659)
            ·
              refine ⟨5567792501348798200325489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3711861667565865466883659 5567792501348798200325489)
              ·
                refine ⟨4175844376011598650244117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5567792501348798200325489 4175844376011598650244117)
                ·
                  refine ⟨195742705125543686730193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4175844376011598650244117 195742705125543686730193)
                  ·
                    rfl

theorem cell22_1715434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 2, 6].length) (baseStart_1715434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715434 prefixEnd_1715434 := by exact prefixLift 1715434
  have htrace : WordTrace (prefixWord ++ tailWord_1715434) baseStart_1715434 baseEnd_1715434 := by
    simpa [prefixWord, tailWord_1715434, baseEnd_1715434] using wordTrace_append hprefix tailTrace_1715434
  have hstable : (prefixWord ++ tailWord_1715434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715434).length < 2 ^ (prefixWord ++ tailWord_1715434).sum := by decide
  have hdescent : baseEnd_1715434 < baseStart_1715434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715444 : List Nat := [2, 6, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_1715444 : Nat := 118140960795 + 1715444 * 2 ^ 59
def prefixEnd_1715444 : Nat := 4983230072969 + 3 ^ 40 * 1715444 * 2
def baseEnd_1715444 : Nat := 587231538580994367440549

theorem tailTrace_1715444 : CollatzResearch.WordTrace tailWord_1715444 prefixEnd_1715444 587231538580994367440549 := by
  unfold tailWord_1715444
  simp only [CollatzResearch.WordTrace]
  refine ⟨31283691398623418677708693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41711588531497891570278257 31283691398623418677708693)
  ·
    refine ⟨1466423034310472750517595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 31283691398623418677708693 1466423034310472750517595)
    ·
      refine ⟨2199634551465709125776393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1466423034310472750517595 2199634551465709125776393)
      ·
        refine ⟨1649725913599281844332295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2199634551465709125776393 1649725913599281844332295)
        ·
          refine ⟨2474588870398922766498443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1649725913599281844332295 2474588870398922766498443)
          ·
            refine ⟨3711883305598384149747665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474588870398922766498443 3711883305598384149747665)
            ·
              refine ⟨2783912479198788112310749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3711883305598384149747665 2783912479198788112310749)
              ·
                refine ⟨1043967179699545542116531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2783912479198788112310749 1043967179699545542116531)
                ·
                  refine ⟨1565950769549318313174797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1043967179699545542116531 1565950769549318313174797)
                  ·
                    refine ⟨587231538580994367440549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565950769549318313174797 587231538580994367440549)
                    ·
                      rfl

theorem cell22_1715444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_1715444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715444 prefixEnd_1715444 := by exact prefixLift 1715444
  have htrace : WordTrace (prefixWord ++ tailWord_1715444) baseStart_1715444 baseEnd_1715444 := by
    simpa [prefixWord, tailWord_1715444, baseEnd_1715444] using wordTrace_append hprefix tailTrace_1715444
  have hstable : (prefixWord ++ tailWord_1715444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715444).length < 2 ^ (prefixWord ++ tailWord_1715444).sum := by decide
  have hdescent : baseEnd_1715444 < baseStart_1715444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715447 : List Nat := [1, 1, 3, 1, 1, 1, 2, 5, 1, 6]
def baseStart_1715447 : Nat := 118140960795 + 1715447 * 2 ^ 59
def prefixEnd_1715447 : Nat := 4983230072969 + 3 ^ 40 * 1715447 * 2
def baseEnd_1715447 : Nat := 587232565542303359615539

theorem tailTrace_1715447 : CollatzResearch.WordTrace tailWord_1715447 prefixEnd_1715447 587232565542303359615539 := by
  unfold tailWord_1715447
  simp only [CollatzResearch.WordTrace]
  refine ⟨62567492216235968867776595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41711661477490645911851063 62567492216235968867776595)
  ·
    refine ⟨93851238324353953301664893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62567492216235968867776595 93851238324353953301664893)
    ·
      refine ⟨35194214371632732488124335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93851238324353953301664893 35194214371632732488124335)
      ·
        refine ⟨52791321557449098732186503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35194214371632732488124335 52791321557449098732186503)
        ·
          refine ⟨79186982336173648098279755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52791321557449098732186503 79186982336173648098279755)
          ·
            refine ⟨118780473504260472147419633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79186982336173648098279755 118780473504260472147419633)
            ·
              refine ⟨89085355128195354110564725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118780473504260472147419633 89085355128195354110564725)
              ·
                refine ⟨8351752043268314447865443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89085355128195354110564725 8351752043268314447865443)
                ·
                  refine ⟨12527628064902471671798165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8351752043268314447865443 12527628064902471671798165)
                  ·
                    refine ⟨587232565542303359615539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12527628064902471671798165 587232565542303359615539)
                    ·
                      rfl

theorem cell22_1715447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 5, 1, 6].length) (baseStart_1715447 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715447 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715447 prefixEnd_1715447 := by exact prefixLift 1715447
  have htrace : WordTrace (prefixWord ++ tailWord_1715447) baseStart_1715447 baseEnd_1715447 := by
    simpa [prefixWord, tailWord_1715447, baseEnd_1715447] using wordTrace_append hprefix tailTrace_1715447
  have hstable : (prefixWord ++ tailWord_1715447).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715447).length < 2 ^ (prefixWord ++ tailWord_1715447).sum := by decide
  have hdescent : baseEnd_1715447 < baseStart_1715447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715449 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 4, 3]
def baseStart_1715449 : Nat := 118140960795 + 1715449 * 2 ^ 59
def prefixEnd_1715449 : Nat := 4983230072969 + 3 ^ 40 * 1715449 * 2
def baseEnd_1715449 : Nat := 587233250183176021065533

theorem tailTrace_1715449 : CollatzResearch.WordTrace tailWord_1715449 prefixEnd_1715449 587233250183176021065533 := by
  unfold tailWord_1715449
  simp only [CollatzResearch.WordTrace]
  refine ⟨62567565162228723209349401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41711710108152482139566267 62567565162228723209349401)
  ·
    refine ⟨46925673871671542407012051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62567565162228723209349401 46925673871671542407012051)
    ·
      refine ⟨70388510807507313610518077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46925673871671542407012051 70388510807507313610518077)
      ·
        refine ⟨26395691552815242603944279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70388510807507313610518077 26395691552815242603944279)
        ·
          refine ⟨39593537329222863905916419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26395691552815242603944279 39593537329222863905916419)
          ·
            refine ⟨59390305993834295858874629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39593537329222863905916419 59390305993834295858874629)
            ·
              refine ⟨11135682373843930473538993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59390305993834295858874629 11135682373843930473538993)
              ·
                refine ⟨8351761780382947855154245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11135682373843930473538993 8351761780382947855154245)
                ·
                  refine ⟨1565955333821802722841421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8351761780382947855154245 1565955333821802722841421)
                  ·
                    refine ⟨587233250183176021065533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1565955333821802722841421 587233250183176021065533)
                    ·
                      rfl

theorem cell22_1715449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 4, 3].length) (baseStart_1715449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715449 prefixEnd_1715449 := by exact prefixLift 1715449
  have htrace : WordTrace (prefixWord ++ tailWord_1715449) baseStart_1715449 baseEnd_1715449 := by
    simpa [prefixWord, tailWord_1715449, baseEnd_1715449] using wordTrace_append hprefix tailTrace_1715449
  have hstable : (prefixWord ++ tailWord_1715449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715449).length < 2 ^ (prefixWord ++ tailWord_1715449).sum := by decide
  have hdescent : baseEnd_1715449 < baseStart_1715449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715496 : List Nat := [2, 1, 5, 1, 2, 1, 4, 6]
def baseStart_1715496 : Nat := 118140960795 + 1715496 * 2 ^ 59
def prefixEnd_1715496 : Nat := 4983230072969 + 3 ^ 40 * 1715496 * 2
def baseEnd_1715496 : Nat := 65249926582631507237821

theorem tailTrace_1715496 : CollatzResearch.WordTrace tailWord_1715496 prefixEnd_1715496 65249926582631507237821 := by
  unfold tailWord_1715496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31284639696529225118155171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41712852928705633490873561 31284639696529225118155171)
  ·
    refine ⟨46926959544793837677232757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31284639696529225118155171 46926959544793837677232757)
    ·
      refine ⟨4399402457324422282240571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46926959544793837677232757 4399402457324422282240571)
      ·
        refine ⟨6599103685986633423360857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4399402457324422282240571 6599103685986633423360857)
        ·
          refine ⟨4949327764489975067520643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6599103685986633423360857 4949327764489975067520643)
          ·
            refine ⟨7423991646734962601280965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4949327764489975067520643 7423991646734962601280965)
            ·
              refine ⟨1391998433762805487740181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7423991646734962601280965 1391998433762805487740181)
              ·
                refine ⟨65249926582631507237821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1391998433762805487740181 65249926582631507237821)
                ·
                  rfl

theorem cell22_1715496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 4, 6].length) (baseStart_1715496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715496 prefixEnd_1715496 := by exact prefixLift 1715496
  have htrace : WordTrace (prefixWord ++ tailWord_1715496) baseStart_1715496 baseEnd_1715496 := by
    simpa [prefixWord, tailWord_1715496, baseEnd_1715496] using wordTrace_append hprefix tailTrace_1715496
  have hstable : (prefixWord ++ tailWord_1715496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715496).length < 2 ^ (prefixWord ++ tailWord_1715496).sum := by decide
  have hdescent : baseEnd_1715496 < baseStart_1715496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715541 : List Nat := [1, 3, 2, 2, 3, 2, 1, 3, 5]
def baseStart_1715541 : Nat := 118140960795 + 1715541 * 2 ^ 59
def prefixEnd_1715541 : Nat := 4983230072969 + 3 ^ 40 * 1715541 * 2
def baseEnd_1715541 : Nat := 195754914554439482588417

theorem tailTrace_1715541 : CollatzResearch.WordTrace tailWord_1715541 prefixEnd_1715541 195754914554439482588417 := by
  unfold tailWord_1715541
  simp only [CollatzResearch.WordTrace]
  refine ⟨62570920677895422921698477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41713947118596948614465651 62570920677895422921698477)
  ·
    refine ⟨23464095254210783595636929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62570920677895422921698477 23464095254210783595636929)
    ·
      refine ⟨17598071440658087696727697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23464095254210783595636929 17598071440658087696727697)
      ·
        refine ⟨13198553580493565772545773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17598071440658087696727697 13198553580493565772545773)
        ·
          refine ⟨4949457592685087164704665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13198553580493565772545773 4949457592685087164704665)
          ·
            refine ⟨3712093194513815373528499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4949457592685087164704665 3712093194513815373528499)
            ·
              refine ⟨5568139791770723060292749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712093194513815373528499 5568139791770723060292749)
              ·
                refine ⟨2088052421914021147609781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5568139791770723060292749 2088052421914021147609781)
                ·
                  refine ⟨195754914554439482588417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2088052421914021147609781 195754914554439482588417)
                  ·
                    rfl

theorem cell22_1715541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 1, 3, 5].length) (baseStart_1715541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715541 prefixEnd_1715541 := by exact prefixLift 1715541
  have htrace : WordTrace (prefixWord ++ tailWord_1715541) baseStart_1715541 baseEnd_1715541 := by
    simpa [prefixWord, tailWord_1715541, baseEnd_1715541] using wordTrace_append hprefix tailTrace_1715541
  have hstable : (prefixWord ++ tailWord_1715541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715541).length < 2 ^ (prefixWord ++ tailWord_1715541).sum := by decide
  have hdescent : baseEnd_1715541 < baseStart_1715541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715652 : List Nat := [2, 3, 3, 2, 1, 2, 3, 1, 2, 3]
def baseStart_1715652 : Nat := 118140960795 + 1715652 * 2 ^ 59
def prefixEnd_1715652 : Nat := 4983230072969 + 3 ^ 40 * 1715652 * 2
def baseEnd_1715652 : Nat := 587302741231751158239911

theorem tailTrace_1715652 : CollatzResearch.WordTrace tailWord_1715652 prefixEnd_1715652 587302741231751158239911 := by
  unfold tailWord_1715652
  simp only [CollatzResearch.WordTrace]
  refine ⟨31287484590246644439494605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41716646120328859252659473 31287484590246644439494605)
  ·
    refine ⟨11732806721342491664810477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31287484590246644439494605 11732806721342491664810477)
    ·
      refine ⟨4399802520503434374303929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11732806721342491664810477 4399802520503434374303929)
      ·
        refine ⟨3299851890377575780727947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4399802520503434374303929 3299851890377575780727947)
        ·
          refine ⟨4949777835566363671091921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3299851890377575780727947 4949777835566363671091921)
          ·
            refine ⟨3712333376674772753318941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4949777835566363671091921 3712333376674772753318941)
            ·
              refine ⟨1392125016253039782494603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3712333376674772753318941 1392125016253039782494603)
              ·
                refine ⟨2088187524379559673741905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392125016253039782494603 2088187524379559673741905)
                ·
                  refine ⟨1566140643284669755306429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2088187524379559673741905 1566140643284669755306429)
                  ·
                    refine ⟨587302741231751158239911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1566140643284669755306429 587302741231751158239911)
                    ·
                      rfl

theorem cell22_1715652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_1715652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715652 prefixEnd_1715652 := by exact prefixLift 1715652
  have htrace : WordTrace (prefixWord ++ tailWord_1715652) baseStart_1715652 baseEnd_1715652 := by
    simpa [prefixWord, tailWord_1715652, baseEnd_1715652] using wordTrace_append hprefix tailTrace_1715652
  have hstable : (prefixWord ++ tailWord_1715652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715652).length < 2 ^ (prefixWord ++ tailWord_1715652).sum := by decide
  have hdescent : baseEnd_1715652 < baseStart_1715652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715689 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 1, 10]
def baseStart_1715689 : Nat := 118140960795 + 1715689 * 2 ^ 59
def prefixEnd_1715689 : Nat := 4983230072969 + 3 ^ 40 * 1715689 * 2
def baseEnd_1715689 : Nat := 587315407087895395064797

theorem tailTrace_1715689 : CollatzResearch.WordTrace tailWord_1715689 prefixEnd_1715689 587315407087895395064797 := by
  unfold tailWord_1715689
  simp only [CollatzResearch.WordTrace]
  refine ⟨62576318681359244198086121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41717545787572829465390747 62576318681359244198086121)
  ·
    refine ⟨46932239011019433148564591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62576318681359244198086121 46932239011019433148564591)
    ·
      refine ⟨70398358516529149722846887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46932239011019433148564591 70398358516529149722846887)
      ·
        refine ⟨105597537774793724584270331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70398358516529149722846887 105597537774793724584270331)
        ·
          refine ⟨158396306662190586876405497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105597537774793724584270331 158396306662190586876405497)
          ·
            refine ⟨118797229996642940157304123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 158396306662190586876405497 118797229996642940157304123)
            ·
              refine ⟨178195844994964410235956185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118797229996642940157304123 178195844994964410235956185)
              ·
                refine ⟨133646883746223307676967139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 178195844994964410235956185 133646883746223307676967139)
                ·
                  refine ⟨200470325619334961515450709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133646883746223307676967139 200470325619334961515450709)
                  ·
                    refine ⟨587315407087895395064797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 200470325619334961515450709 587315407087895395064797)
                    ·
                      rfl

theorem cell22_1715689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_1715689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715689 prefixEnd_1715689 := by exact prefixLift 1715689
  have htrace : WordTrace (prefixWord ++ tailWord_1715689) baseStart_1715689 baseEnd_1715689 := by
    simpa [prefixWord, tailWord_1715689, baseEnd_1715689] using wordTrace_append hprefix tailTrace_1715689
  have hstable : (prefixWord ++ tailWord_1715689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715689).length < 2 ^ (prefixWord ++ tailWord_1715689).sum := by decide
  have hdescent : baseEnd_1715689 < baseStart_1715689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715697 : List Nat := [1, 2, 2, 2, 3, 3, 3, 2, 1, 3]
def baseStart_1715697 : Nat := 118140960795 + 1715697 * 2 ^ 59
def prefixEnd_1715697 : Nat := 4983230072969 + 3 ^ 40 * 1715697 * 2
def baseEnd_1715697 : Nat := 587318145651386040864773

theorem tailTrace_1715697 : CollatzResearch.WordTrace tailWord_1715697 prefixEnd_1715697 587318145651386040864773 := by
  unfold tailWord_1715697
  simp only [CollatzResearch.WordTrace]
  refine ⟨62576610465330261564377345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41717740310220174376251563 62576610465330261564377345)
  ·
    refine ⟨46932457848997696173283009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62576610465330261564377345 46932457848997696173283009)
    ·
      refine ⟨35199343386748272129962257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46932457848997696173283009 35199343386748272129962257)
      ·
        refine ⟨26399507540061204097471693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35199343386748272129962257 26399507540061204097471693)
        ·
          refine ⟨9899815327522951536551885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26399507540061204097471693 9899815327522951536551885)
          ·
            refine ⟨3712430747821106826206957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9899815327522951536551885 3712430747821106826206957)
            ·
              refine ⟨1392161530432915059827609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3712430747821106826206957 1392161530432915059827609)
              ·
                refine ⟨1044121147824686294870707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392161530432915059827609 1044121147824686294870707)
                ·
                  refine ⟨1566181721737029442306061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044121147824686294870707 1566181721737029442306061)
                  ·
                    refine ⟨587318145651386040864773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1566181721737029442306061 587318145651386040864773)
                    ·
                      rfl

theorem cell22_1715697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 2, 1, 3].length) (baseStart_1715697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715697 prefixEnd_1715697 := by exact prefixLift 1715697
  have htrace : WordTrace (prefixWord ++ tailWord_1715697) baseStart_1715697 baseEnd_1715697 := by
    simpa [prefixWord, tailWord_1715697, baseEnd_1715697] using wordTrace_append hprefix tailTrace_1715697
  have hstable : (prefixWord ++ tailWord_1715697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715697).length < 2 ^ (prefixWord ++ tailWord_1715697).sum := by decide
  have hdescent : baseEnd_1715697 < baseStart_1715697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715706 : List Nat := [3, 1, 1, 1, 1, 2, 4, 2, 3, 4]
def baseStart_1715706 : Nat := 118140960795 + 1715706 * 2 ^ 59
def prefixEnd_1715706 : Nat := 4983230072969 + 3 ^ 40 * 1715706 * 2
def baseEnd_1715706 : Nat := 587321226535313017389745

theorem tailTrace_1715706 : CollatzResearch.WordTrace tailWord_1715706 prefixEnd_1715706 587321226535313017389745 := by
  unfold tailWord_1715706
  simp only [CollatzResearch.WordTrace]
  refine ⟨15644234680574414025363743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41717959148198437400969981 15644234680574414025363743)
  ·
    refine ⟨23466352020861621038045615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15644234680574414025363743 23466352020861621038045615)
    ·
      refine ⟨35199528031292431557068423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23466352020861621038045615 35199528031292431557068423)
      ·
        refine ⟨52799292046938647335602635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35199528031292431557068423 52799292046938647335602635)
        ·
          refine ⟨79198938070407971003403953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52799292046938647335602635 79198938070407971003403953)
          ·
            refine ⟨59399203552805978252552965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79198938070407971003403953 59399203552805978252552965)
            ·
              refine ⟨11137350666151120922353681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59399203552805978252552965 11137350666151120922353681)
              ·
                refine ⟨8353012999613340691765261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11137350666151120922353681 8353012999613340691765261)
                ·
                  refine ⟨3132379874855002759411973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8353012999613340691765261 3132379874855002759411973)
                  ·
                    refine ⟨587321226535313017389745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3132379874855002759411973 587321226535313017389745)
                    ·
                      rfl

theorem cell22_1715706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 4, 2, 3, 4].length) (baseStart_1715706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715706 prefixEnd_1715706 := by exact prefixLift 1715706
  have htrace : WordTrace (prefixWord ++ tailWord_1715706) baseStart_1715706 baseEnd_1715706 := by
    simpa [prefixWord, tailWord_1715706, baseEnd_1715706] using wordTrace_append hprefix tailTrace_1715706
  have hstable : (prefixWord ++ tailWord_1715706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715706).length < 2 ^ (prefixWord ++ tailWord_1715706).sum := by decide
  have hdescent : baseEnd_1715706 < baseStart_1715706 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715723 : List Nat := [1, 1, 1, 1, 8, 1, 1, 1, 3, 4]
def baseStart_1715723 : Nat := 118140960795 + 1715723 * 2 ^ 59
def prefixEnd_1715723 : Nat := 4983230072969 + 3 ^ 40 * 1715723 * 2
def baseEnd_1715723 : Nat := 587327045982730639714693

theorem tailTrace_1715723 : CollatzResearch.WordTrace tailWord_1715723 prefixEnd_1715723 587327045982730639714693 := by
  unfold tailWord_1715723
  simp only [CollatzResearch.WordTrace]
  refine ⟨62577558763236068004823823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41718372508824045336549215 62577558763236068004823823)
  ·
    refine ⟨93866338144854102007235735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62577558763236068004823823 93866338144854102007235735)
    ·
      refine ⟨140799507217281153010853603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93866338144854102007235735 140799507217281153010853603)
      ·
        refine ⟨211199260825921729516280405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140799507217281153010853603 211199260825921729516280405)
        ·
          refine ⟨2474991337803770267768911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 211199260825921729516280405 2474991337803770267768911)
          ·
            refine ⟨3712487006705655401653367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2474991337803770267768911 3712487006705655401653367)
            ·
              refine ⟨5568730510058483102480051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3712487006705655401653367 5568730510058483102480051)
              ·
                refine ⟨8353095765087724653720077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5568730510058483102480051 8353095765087724653720077)
                ·
                  refine ⟨3132410911907896745145029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8353095765087724653720077 3132410911907896745145029)
                  ·
                    refine ⟨587327045982730639714693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3132410911907896745145029 587327045982730639714693)
                    ·
                      rfl

theorem cell22_1715723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 1, 1, 1, 3, 4].length) (baseStart_1715723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715723 prefixEnd_1715723 := by exact prefixLift 1715723
  have htrace : WordTrace (prefixWord ++ tailWord_1715723) baseStart_1715723 baseEnd_1715723 := by
    simpa [prefixWord, tailWord_1715723, baseEnd_1715723] using wordTrace_append hprefix tailTrace_1715723
  have hstable : (prefixWord ++ tailWord_1715723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715723).length < 2 ^ (prefixWord ++ tailWord_1715723).sum := by decide
  have hdescent : baseEnd_1715723 < baseStart_1715723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715738 : List Nat := [3, 1, 1, 3, 1, 1, 1, 7, 4]
def baseStart_1715738 : Nat := 118140960795 + 1715738 * 2 ^ 59
def prefixEnd_1715738 : Nat := 4983230072969 + 3 ^ 40 * 1715738 * 2
def baseEnd_1715738 : Nat := 195777393596425200196549

theorem tailTrace_1715738 : CollatzResearch.WordTrace tailWord_1715738 prefixEnd_1715738 195777393596425200196549 := by
  unfold tailWord_1715738
  simp only [CollatzResearch.WordTrace]
  refine ⟨15644526464545431391654967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41718737238787817044413245 15644526464545431391654967)
  ·
    refine ⟨23466789696818147087482451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15644526464545431391654967 23466789696818147087482451)
    ·
      refine ⟨35200184545227220631223677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23466789696818147087482451 35200184545227220631223677)
      ·
        refine ⟨13200069204460207736708879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35200184545227220631223677 13200069204460207736708879)
        ·
          refine ⟨19800103806690311605063319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13200069204460207736708879 19800103806690311605063319)
          ·
            refine ⟨29700155710035467407594979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19800103806690311605063319 29700155710035467407594979)
            ·
              refine ⟨44550233565053201111392469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29700155710035467407594979 44550233565053201111392469)
              ·
                refine ⟨1044146099180934401048261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 44550233565053201111392469 1044146099180934401048261)
                ·
                  refine ⟨195777393596425200196549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044146099180934401048261 195777393596425200196549)
                  ·
                    rfl

theorem cell22_1715738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_1715738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715738 prefixEnd_1715738 := by exact prefixLift 1715738
  have htrace : WordTrace (prefixWord ++ tailWord_1715738) baseStart_1715738 baseEnd_1715738 := by
    simpa [prefixWord, tailWord_1715738, baseEnd_1715738] using wordTrace_append hprefix tailTrace_1715738
  have hstable : (prefixWord ++ tailWord_1715738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715738).length < 2 ^ (prefixWord ++ tailWord_1715738).sum := by decide
  have hdescent : baseEnd_1715738 < baseStart_1715738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715740 : List Nat := [2, 2, 3, 1, 2, 1, 5, 1, 1, 4]
def baseStart_1715740 : Nat := 118140960795 + 1715740 * 2 ^ 59
def prefixEnd_1715740 : Nat := 4983230072969 + 3 ^ 40 * 1715740 * 2
def baseEnd_1715740 : Nat := 587332865430148262039641

theorem tailTrace_1715740 : CollatzResearch.WordTrace tailWord_1715740 prefixEnd_1715740 587332865430148262039641 := by
  unfold tailWord_1715740
  simp only [CollatzResearch.WordTrace]
  refine ⟨31289089402087239954096337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41718785869449653272128449 31289089402087239954096337)
  ·
    refine ⟨23466817051565429965572253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31289089402087239954096337 23466817051565429965572253)
    ·
      refine ⟨8800056394337036237089595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23466817051565429965572253 8800056394337036237089595)
      ·
        refine ⟨13200084591505554355634393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8800056394337036237089595 13200084591505554355634393)
        ·
          refine ⟨9900063443629165766725795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13200084591505554355634393 9900063443629165766725795)
          ·
            refine ⟨14850095165443748650088693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9900063443629165766725795 14850095165443748650088693)
            ·
              refine ⟨1392196421760351435945815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14850095165443748650088693 1392196421760351435945815)
              ·
                refine ⟨2088294632640527153918723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1392196421760351435945815 2088294632640527153918723)
                ·
                  refine ⟨3132441948960790730878085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088294632640527153918723 3132441948960790730878085)
                  ·
                    refine ⟨587332865430148262039641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3132441948960790730878085 587332865430148262039641)
                    ·
                      rfl

theorem cell22_1715740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_1715740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715740 prefixEnd_1715740 := by exact prefixLift 1715740
  have htrace : WordTrace (prefixWord ++ tailWord_1715740) baseStart_1715740 baseEnd_1715740 := by
    simpa [prefixWord, tailWord_1715740, baseEnd_1715740] using wordTrace_append hprefix tailTrace_1715740
  have hstable : (prefixWord ++ tailWord_1715740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715740).length < 2 ^ (prefixWord ++ tailWord_1715740).sum := by decide
  have hdescent : baseEnd_1715740 < baseStart_1715740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715856 : List Nat := [2, 1, 1, 1, 1, 1, 3, 4, 8]
def baseStart_1715856 : Nat := 118140960795 + 1715856 * 2 ^ 59
def prefixEnd_1715856 : Nat := 4983230072969 + 3 ^ 40 * 1715856 * 2
def baseEnd_1715856 : Nat := 195790858200254208713095

theorem tailTrace_1715856 : CollatzResearch.WordTrace tailWord_1715856 prefixEnd_1715856 195790858200254208713095 := by
  unfold tailWord_1715856
  simp only [CollatzResearch.WordTrace]
  refine ⟨31291204835877115859707711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41721606447836154479610281 31291204835877115859707711)
  ·
    refine ⟨46936807253815673789561567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31291204835877115859707711 46936807253815673789561567)
    ·
      refine ⟨70405210880723510684342351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46936807253815673789561567 70405210880723510684342351)
      ·
        refine ⟨105607816321085266026513527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70405210880723510684342351 105607816321085266026513527)
        ·
          refine ⟨158411724481627899039770291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105607816321085266026513527 158411724481627899039770291)
          ·
            refine ⟨237617586722441848559655437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 158411724481627899039770291 237617586722441848559655437)
            ·
              refine ⟨89106595020915693209870789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 237617586722441848559655437 89106595020915693209870789)
              ·
                refine ⟨16707486566421692476850773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 89106595020915693209870789 16707486566421692476850773)
                ·
                  refine ⟨195790858200254208713095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16707486566421692476850773 195790858200254208713095)
                  ·
                    rfl

theorem cell22_1715856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 4, 8].length) (baseStart_1715856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715856 prefixEnd_1715856 := by exact prefixLift 1715856
  have htrace : WordTrace (prefixWord ++ tailWord_1715856) baseStart_1715856 baseEnd_1715856 := by
    simpa [prefixWord, tailWord_1715856, baseEnd_1715856] using wordTrace_append hprefix tailTrace_1715856
  have hstable : (prefixWord ++ tailWord_1715856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715856).length < 2 ^ (prefixWord ++ tailWord_1715856).sum := by decide
  have hdescent : baseEnd_1715856 < baseStart_1715856 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715922 : List Nat := [3, 2, 2, 2, 2, 1, 1, 4, 2, 3]
def baseStart_1715922 : Nat := 118140960795 + 1715922 * 2 ^ 59
def prefixEnd_1715922 : Nat := 4983230072969 + 3 ^ 40 * 1715922 * 2
def baseEnd_1715922 : Nat := 587395167749560453989083

theorem tailTrace_1715922 : CollatzResearch.WordTrace tailWord_1715922 prefixEnd_1715922 587395167749560453989083 := by
  unfold tailWord_1715922
  simp only [CollatzResearch.WordTrace]
  refine ⟨15646204222378781247829505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41723211259676749994212013 15646204222378781247829505)
  ·
    refine ⟨11734653166784085935872129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15646204222378781247829505 11734653166784085935872129)
    ·
      refine ⟨8800989875088064451904097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11734653166784085935872129 8800989875088064451904097)
      ·
        refine ⟨6600742406316048338928073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8800989875088064451904097 6600742406316048338928073)
        ·
          refine ⟨4950556804737036254196055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6600742406316048338928073 4950556804737036254196055)
          ·
            refine ⟨7425835207105554381294083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950556804737036254196055 7425835207105554381294083)
            ·
              refine ⟨11138752810658331571941125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7425835207105554381294083 11138752810658331571941125)
              ·
                refine ⟨2088516151998437169738961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11138752810658331571941125 2088516151998437169738961)
                ·
                  refine ⟨1566387113998827877304221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2088516151998437169738961 1566387113998827877304221)
                  ·
                    refine ⟨587395167749560453989083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1566387113998827877304221 587395167749560453989083)
                    ·
                      rfl

theorem cell22_1715922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 1, 4, 2, 3].length) (baseStart_1715922 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715922 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715922 prefixEnd_1715922 := by exact prefixLift 1715922
  have htrace : WordTrace (prefixWord ++ tailWord_1715922) baseStart_1715922 baseEnd_1715922 := by
    simpa [prefixWord, tailWord_1715922, baseEnd_1715922] using wordTrace_append hprefix tailTrace_1715922
  have hstable : (prefixWord ++ tailWord_1715922).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715922).length < 2 ^ (prefixWord ++ tailWord_1715922).sum := by decide
  have hdescent : baseEnd_1715922 < baseStart_1715922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715924 : List Nat := [2, 4, 1, 3, 1, 1, 4, 2, 4]
def baseStart_1715924 : Nat := 118140960795 + 1715924 * 2 ^ 59
def prefixEnd_1715924 : Nat := 4983230072969 + 3 ^ 40 * 1715924 * 2
def baseEnd_1715924 : Nat := 195798617463477705146359

theorem tailTrace_1715924 : CollatzResearch.WordTrace tailWord_1715924 prefixEnd_1715924 195798617463477705146359 := by
  unfold tailWord_1715924
  simp only [CollatzResearch.WordTrace]
  refine ⟨31292444917753939666445413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41723259890338586221927217 31292444917753939666445413)
  ·
    refine ⟨5867333422078863687458515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31292444917753939666445413 5867333422078863687458515)
    ·
      refine ⟨8801000133118295531187773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5867333422078863687458515 8801000133118295531187773)
      ·
        refine ⟨3300375049919360824195415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8801000133118295531187773 3300375049919360824195415)
        ·
          refine ⟨4950562574879041236293123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3300375049919360824195415 4950562574879041236293123)
          ·
            refine ⟨7425843862318561854439685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4950562574879041236293123 7425843862318561854439685)
            ·
              refine ⟨1392345724184730347707441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7425843862318561854439685 1392345724184730347707441)
              ·
                refine ⟨1044259293138547760780581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392345724184730347707441 1044259293138547760780581)
                ·
                  refine ⟨195798617463477705146359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044259293138547760780581 195798617463477705146359)
                  ·
                    rfl

theorem cell22_1715924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 4, 2, 4].length) (baseStart_1715924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715924 prefixEnd_1715924 := by exact prefixLift 1715924
  have htrace : WordTrace (prefixWord ++ tailWord_1715924) baseStart_1715924 baseEnd_1715924 := by
    simpa [prefixWord, tailWord_1715924, baseEnd_1715924] using wordTrace_append hprefix tailTrace_1715924
  have hstable : (prefixWord ++ tailWord_1715924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715924).length < 2 ^ (prefixWord ++ tailWord_1715924).sum := by decide
  have hdescent : baseEnd_1715924 < baseStart_1715924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715967 : List Nat := [1, 1, 2, 2, 1, 3, 3, 5, 1, 3]
def baseStart_1715967 : Nat := 118140960795 + 1715967 * 2 ^ 59
def prefixEnd_1715967 : Nat := 4983230072969 + 3 ^ 40 * 1715967 * 2
def baseEnd_1715967 : Nat := 587410572169195336613945

theorem tailTrace_1715967 : CollatzResearch.WordTrace tailWord_1715967 prefixEnd_1715967 587410572169195336613945 := by
  unfold tailWord_1715967
  simp only [CollatzResearch.WordTrace]
  refine ⟨62586458174352097676706155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41724305449568065117804103 62586458174352097676706155)
  ·
    refine ⟨93879687261528146515059233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62586458174352097676706155 93879687261528146515059233)
    ·
      refine ⟨70409765446146109886294425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93879687261528146515059233 70409765446146109886294425)
      ·
        refine ⟨52807324084609582414720819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70409765446146109886294425 52807324084609582414720819)
        ·
          refine ⟨79210986126914373622081229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52807324084609582414720819 79210986126914373622081229)
          ·
            refine ⟨29704119797592890108280461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79210986126914373622081229 29704119797592890108280461)
            ·
              refine ⟨11139044924097333790605173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29704119797592890108280461 11139044924097333790605173)
              ·
                refine ⟨1044285461634125042869235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11139044924097333790605173 1044285461634125042869235)
                ·
                  refine ⟨1566428192451187564303853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044285461634125042869235 1566428192451187564303853)
                  ·
                    refine ⟨587410572169195336613945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1566428192451187564303853 587410572169195336613945)
                    ·
                      rfl

theorem cell22_1715967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 5, 1, 3].length) (baseStart_1715967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715967 prefixEnd_1715967 := by exact prefixLift 1715967
  have htrace : WordTrace (prefixWord ++ tailWord_1715967) baseStart_1715967 baseEnd_1715967 := by
    simpa [prefixWord, tailWord_1715967, baseEnd_1715967] using wordTrace_append hprefix tailTrace_1715967
  have hstable : (prefixWord ++ tailWord_1715967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715967).length < 2 ^ (prefixWord ++ tailWord_1715967).sum := by decide
  have hdescent : baseEnd_1715967 < baseStart_1715967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1715980 : List Nat := [2, 2, 1, 2, 2, 1, 5, 2, 5]
def baseStart_1715980 : Nat := 118140960795 + 1715980 * 2 ^ 59
def prefixEnd_1715980 : Nat := 4983230072969 + 3 ^ 40 * 1715980 * 2
def baseEnd_1715980 : Nat := 195805007444955878679635

theorem tailTrace_1715980 : CollatzResearch.WordTrace tailWord_1715980 prefixEnd_1715980 195805007444955878679635 := by
  unfold tailWord_1715980
  simp only [CollatzResearch.WordTrace]
  refine ⟨31293466161652500448464697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41724621548870000597952929 31293466161652500448464697)
  ·
    refine ⟨23470099621239375336348523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31293466161652500448464697 23470099621239375336348523)
    ·
      refine ⟨35205149431859063004522785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23470099621239375336348523 35205149431859063004522785)
      ·
        refine ⟨26403862073894297253392089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35205149431859063004522785 26403862073894297253392089)
        ·
          refine ⟨19802896555420722940044067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26403862073894297253392089 19802896555420722940044067)
          ·
            refine ⟨29704344833131084410066101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19802896555420722940044067 29704344833131084410066101)
            ·
              refine ⟨2784782328106039163443697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29704344833131084410066101 2784782328106039163443697)
              ·
                refine ⟨2088586746079529372582773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2784782328106039163443697 2088586746079529372582773)
                ·
                  refine ⟨195805007444955878679635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2088586746079529372582773 195805007444955878679635)
                  ·
                    rfl

theorem cell22_1715980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 5, 2, 5].length) (baseStart_1715980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1715980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1715980 prefixEnd_1715980 := by exact prefixLift 1715980
  have htrace : WordTrace (prefixWord ++ tailWord_1715980) baseStart_1715980 baseEnd_1715980 := by
    simpa [prefixWord, tailWord_1715980, baseEnd_1715980] using wordTrace_append hprefix tailTrace_1715980
  have hstable : (prefixWord ++ tailWord_1715980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1715980).length < 2 ^ (prefixWord ++ tailWord_1715980).sum := by decide
  have hdescent : baseEnd_1715980 < baseStart_1715980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1715980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716057 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 2, 3]
def baseStart_1716057 : Nat := 118140960795 + 1716057 * 2 ^ 59
def prefixEnd_1716057 : Nat := 4983230072969 + 3 ^ 40 * 1716057 * 2
def baseEnd_1716057 : Nat := 587441381008465101863669

theorem tailTrace_1716057 : CollatzResearch.WordTrace tailWord_1716057 prefixEnd_1716057 587441381008465101863669 := by
  unfold tailWord_1716057
  simp only [CollatzResearch.WordTrace]
  refine ⟨62589740744026043047482425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41726493829350695364988283 62589740744026043047482425)
  ·
    refine ⟨46942305558019532285611819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62589740744026043047482425 46942305558019532285611819)
    ·
      refine ⟨70413458337029298428417729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46942305558019532285611819 70413458337029298428417729)
      ·
        refine ⟨52810093752771973821313297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70413458337029298428417729 52810093752771973821313297)
        ·
          refine ⟨39607570314578980365984973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52810093752771973821313297 39607570314578980365984973)
          ·
            refine ⟨14852838867967117637244365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39607570314578980365984973 14852838867967117637244365)
            ·
              refine ⟨5569814575487669113966637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14852838867967117637244365 5569814575487669113966637)
              ·
                refine ⟨2088680465807875917737489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5569814575487669113966637 2088680465807875917737489)
                ·
                  refine ⟨1566510349355906938303117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2088680465807875917737489 1566510349355906938303117)
                  ·
                    refine ⟨587441381008465101863669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1566510349355906938303117 587441381008465101863669)
                    ·
                      rfl

theorem cell22_1716057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 2, 3].length) (baseStart_1716057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716057 prefixEnd_1716057 := by exact prefixLift 1716057
  have htrace : WordTrace (prefixWord ++ tailWord_1716057) baseStart_1716057 baseEnd_1716057 := by
    simpa [prefixWord, tailWord_1716057, baseEnd_1716057] using wordTrace_append hprefix tailTrace_1716057
  have hstable : (prefixWord ++ tailWord_1716057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716057).length < 2 ^ (prefixWord ++ tailWord_1716057).sum := by decide
  have hdescent : baseEnd_1716057 < baseStart_1716057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716072 : List Nat := [2, 1, 4, 2, 1, 1, 4, 1, 2, 4]
def baseStart_1716072 : Nat := 118140960795 + 1716072 * 2 ^ 59
def prefixEnd_1716072 : Nat := 4983230072969 + 3 ^ 40 * 1716072 * 2
def baseEnd_1716072 : Nat := 587446515815010062738623

theorem tailTrace_1716072 : CollatzResearch.WordTrace tailWord_1716072 prefixEnd_1716072 587446515815010062738623 := by
  unfold tailWord_1716072
  simp only [CollatzResearch.WordTrace]
  refine ⟨31295143919485850304639235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41726858559314467072852313 31295143919485850304639235)
  ·
    refine ⟨46942715879228775456958853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31295143919485850304639235 46942715879228775456958853)
    ·
      refine ⟨8801759227355395398179785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46942715879228775456958853 8801759227355395398179785)
      ·
        refine ⟨6601319420516546548634839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8801759227355395398179785 6601319420516546548634839)
        ·
          refine ⟨9901979130774819822952259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6601319420516546548634839 9901979130774819822952259)
          ·
            refine ⟨14852968696162229734428389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9901979130774819822952259 14852968696162229734428389)
            ·
              refine ⟨2784931630530418075205323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14852968696162229734428389 2784931630530418075205323)
              ·
                refine ⟨4177397445795627112807985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2784931630530418075205323 4177397445795627112807985)
                ·
                  refine ⟨3133048084346720334605989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4177397445795627112807985 3133048084346720334605989)
                  ·
                    refine ⟨587446515815010062738623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133048084346720334605989 587446515815010062738623)
                    ·
                      rfl

theorem cell22_1716072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 2, 4].length) (baseStart_1716072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716072 prefixEnd_1716072 := by exact prefixLift 1716072
  have htrace : WordTrace (prefixWord ++ tailWord_1716072) baseStart_1716072 baseEnd_1716072 := by
    simpa [prefixWord, tailWord_1716072, baseEnd_1716072] using wordTrace_append hprefix tailTrace_1716072
  have hstable : (prefixWord ++ tailWord_1716072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716072).length < 2 ^ (prefixWord ++ tailWord_1716072).sum := by decide
  have hdescent : baseEnd_1716072 < baseStart_1716072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716074 : List Nat := [3, 1, 3, 4, 1, 1, 1, 2, 1, 5]
def baseStart_1716074 : Nat := 118140960795 + 1716074 * 2 ^ 59
def prefixEnd_1716074 : Nat := 4983230072969 + 3 ^ 40 * 1716074 * 2
def baseEnd_1716074 : Nat := 587447200455882724188617

theorem tailTrace_1716074 : CollatzResearch.WordTrace tailWord_1716074 prefixEnd_1716074 587447200455882724188617 := by
  unfold tailWord_1716074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15647590196241113737712819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41726907189976303300567517 15647590196241113737712819)
  ·
    refine ⟨23471385294361670606569229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15647590196241113737712819 23471385294361670606569229)
    ·
      refine ⟨8801769485385626477463461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23471385294361670606569229 8801769485385626477463461)
      ·
        refine ⟨1650331778509804964524399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8801769485385626477463461 1650331778509804964524399)
        ·
          refine ⟨2475497667764707446786599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650331778509804964524399 2475497667764707446786599)
          ·
            refine ⟨3713246501647061170179899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475497667764707446786599 3713246501647061170179899)
            ·
              refine ⟨5569869752470591755269849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3713246501647061170179899 5569869752470591755269849)
              ·
                refine ⟨4177402314352943816452387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5569869752470591755269849 4177402314352943816452387)
                ·
                  refine ⟨6266103471529415724678581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4177402314352943816452387 6266103471529415724678581)
                  ·
                    refine ⟨587447200455882724188617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6266103471529415724678581 587447200455882724188617)
                    ·
                      rfl

theorem cell22_1716074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_1716074 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716074 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716074 prefixEnd_1716074 := by exact prefixLift 1716074
  have htrace : WordTrace (prefixWord ++ tailWord_1716074) baseStart_1716074 baseEnd_1716074 := by
    simpa [prefixWord, tailWord_1716074, baseEnd_1716074] using wordTrace_append hprefix tailTrace_1716074
  have hstable : (prefixWord ++ tailWord_1716074).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716074).length < 2 ^ (prefixWord ++ tailWord_1716074).sum := by decide
  have hdescent : baseEnd_1716074 < baseStart_1716074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716100 : List Nat := [2, 3, 2, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1716100 : Nat := 118140960795 + 1716100 * 2 ^ 59
def prefixEnd_1716100 : Nat := 4983230072969 + 3 ^ 40 * 1716100 * 2
def baseEnd_1716100 : Nat := 587456100787227323038537

theorem tailTrace_1716100 : CollatzResearch.WordTrace tailWord_1716100 prefixEnd_1716100 587456100787227323038537 := by
  unfold tailWord_1716100
  simp only [CollatzResearch.WordTrace]
  refine ⟨31295654541435130695648877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41727539388580174260865169 31295654541435130695648877)
  ·
    refine ⟨11735870453038174010868329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31295654541435130695648877 11735870453038174010868329)
    ·
      refine ⟨8801902839778630508151247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11735870453038174010868329 8801902839778630508151247)
      ·
        refine ⟨13202854259667945762226871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8801902839778630508151247 13202854259667945762226871)
        ·
          refine ⟨19804281389501918643340307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13202854259667945762226871 19804281389501918643340307)
          ·
            refine ⟨29706422084252877965010461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19804281389501918643340307 29706422084252877965010461)
            ·
              refine ⟨11139908281594829236878923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29706422084252877965010461 11139908281594829236878923)
              ·
                refine ⟨16709862422392243855318385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11139908281594829236878923 16709862422392243855318385)
                ·
                  refine ⟨12532396816794182891488789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16709862422392243855318385 12532396816794182891488789)
                  ·
                    refine ⟨587456100787227323038537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12532396816794182891488789 587456100787227323038537)
                    ·
                      rfl

theorem cell22_1716100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1716100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716100 prefixEnd_1716100 := by exact prefixLift 1716100
  have htrace : WordTrace (prefixWord ++ tailWord_1716100) baseStart_1716100 baseEnd_1716100 := by
    simpa [prefixWord, tailWord_1716100, baseEnd_1716100] using wordTrace_append hprefix tailTrace_1716100
  have hstable : (prefixWord ++ tailWord_1716100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716100).length < 2 ^ (prefixWord ++ tailWord_1716100).sum := by decide
  have hdescent : baseEnd_1716100 < baseStart_1716100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716104 : List Nat := [2, 1, 3, 3, 4, 1, 1, 7]
def baseStart_1716104 : Nat := 118140960795 + 1716104 * 2 ^ 59
def prefixEnd_1716104 : Nat := 4983230072969 + 3 ^ 40 * 1716104 * 2
def baseEnd_1716104 : Nat := 65273052229885849548725

theorem tailTrace_1716104 : CollatzResearch.WordTrace tailWord_1716104 prefixEnd_1716104 65273052229885849548725 := by
  unfold tailWord_1716104
  simp only [CollatzResearch.WordTrace]
  refine ⟨31295727487427885037221683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41727636649903846716295577 31295727487427885037221683)
  ·
    refine ⟨46943591231141827555832525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31295727487427885037221683 46943591231141827555832525)
    ·
      refine ⟨17603846711678185333437197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46943591231141827555832525 17603846711678185333437197)
      ·
        refine ⟨6601442516879319500038949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17603846711678185333437197 6601442516879319500038949)
        ·
          refine ⟨1237770471914872406257303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6601442516879319500038949 1237770471914872406257303)
          ·
            refine ⟨1856655707872308609385955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237770471914872406257303 1856655707872308609385955)
            ·
              refine ⟨2784983561808462914078933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856655707872308609385955 2784983561808462914078933)
              ·
                refine ⟨65273052229885849548725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2784983561808462914078933 65273052229885849548725)
                ·
                  rfl

theorem cell22_1716104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 1, 7].length) (baseStart_1716104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716104 prefixEnd_1716104 := by exact prefixLift 1716104
  have htrace : WordTrace (prefixWord ++ tailWord_1716104) baseStart_1716104 baseEnd_1716104 := by
    simpa [prefixWord, tailWord_1716104, baseEnd_1716104] using wordTrace_append hprefix tailTrace_1716104
  have hstable : (prefixWord ++ tailWord_1716104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716104).length < 2 ^ (prefixWord ++ tailWord_1716104).sum := by decide
  have hdescent : baseEnd_1716104 < baseStart_1716104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716142 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1716142 : Nat := 118140960795 + 1716142 * 2 ^ 59
def prefixEnd_1716142 : Nat := 4983230072969 + 3 ^ 40 * 1716142 * 2
def baseEnd_1716142 : Nat := 587470478245553213488409

theorem tailTrace_1716142 : CollatzResearch.WordTrace tailWord_1716142 prefixEnd_1716142 587470478245553213488409 := by
  unfold tailWord_1716142
  simp only [CollatzResearch.WordTrace]
  refine ⟨7824105118589762820540835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41728560632478735042884453 7824105118589762820540835)
  ·
    refine ⟨11736157677884644230811253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7824105118589762820540835 11736157677884644230811253)
    ·
      refine ⟨1100264782301685396638555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11736157677884644230811253 1100264782301685396638555)
      ·
        refine ⟨1650397173452528094957833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1100264782301685396638555 1650397173452528094957833)
        ·
          refine ⟨1237797880089396071218375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1650397173452528094957833 1237797880089396071218375)
          ·
            refine ⟨1856696820134094106827563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1237797880089396071218375 1856696820134094106827563)
            ·
              refine ⟨2785045230201141160241345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856696820134094106827563 2785045230201141160241345)
              ·
                refine ⟨2088783922650855870181009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2785045230201141160241345 2088783922650855870181009)
                ·
                  refine ⟨1566587941988141902635757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2088783922650855870181009 1566587941988141902635757)
                  ·
                    refine ⟨587470478245553213488409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1566587941988141902635757 587470478245553213488409)
                    ·
                      rfl

theorem cell22_1716142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1716142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716142 prefixEnd_1716142 := by exact prefixLift 1716142
  have htrace : WordTrace (prefixWord ++ tailWord_1716142) baseStart_1716142 baseEnd_1716142 := by
    simpa [prefixWord, tailWord_1716142, baseEnd_1716142] using wordTrace_append hprefix tailTrace_1716142
  have hstable : (prefixWord ++ tailWord_1716142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716142).length < 2 ^ (prefixWord ++ tailWord_1716142).sum := by decide
  have hdescent : baseEnd_1716142 < baseStart_1716142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716149 : List Nat := [1, 3, 3, 2, 1, 4, 1, 2, 5]
def baseStart_1716149 : Nat := 118140960795 + 1716149 * 2 ^ 59
def prefixEnd_1716149 : Nat := 4983230072969 + 3 ^ 40 * 1716149 * 2
def baseEnd_1716149 : Nat := 195824291496202509521129

theorem tailTrace_1716149 : CollatzResearch.WordTrace tailWord_1716149 prefixEnd_1716149 195824291496202509521129 := by
  unfold tailWord_1716149
  simp only [CollatzResearch.WordTrace]
  refine ⟨62593096259692742759831501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41728730839795161839887667 62593096259692742759831501)
  ·
    refine ⟨23472411097384778534936813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62593096259692742759831501 23472411097384778534936813)
    ·
      refine ⟨8802154161519291950601305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23472411097384778534936813 8802154161519291950601305)
      ·
        refine ⟨6601615621139468962950979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8802154161519291950601305 6601615621139468962950979)
        ·
          refine ⟨9902423431709203444426469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6601615621139468962950979 9902423431709203444426469)
          ·
            refine ⟨1856704393445475645829963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9902423431709203444426469 1856704393445475645829963)
            ·
              refine ⟨2785056590168213468744945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1856704393445475645829963 2785056590168213468744945)
              ·
                refine ⟨2088792442626160101558709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2785056590168213468744945 2088792442626160101558709)
                ·
                  refine ⟨195824291496202509521129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2088792442626160101558709 195824291496202509521129)
                  ·
                    rfl

theorem cell22_1716149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 2, 5].length) (baseStart_1716149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716149 prefixEnd_1716149 := by exact prefixLift 1716149
  have htrace : WordTrace (prefixWord ++ tailWord_1716149) baseStart_1716149 baseEnd_1716149 := by
    simpa [prefixWord, tailWord_1716149, baseEnd_1716149] using wordTrace_append hprefix tailTrace_1716149
  have hstable : (prefixWord ++ tailWord_1716149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716149).length < 2 ^ (prefixWord ++ tailWord_1716149).sum := by decide
  have hdescent : baseEnd_1716149 < baseStart_1716149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716207 : List Nat := [1, 1, 2, 1, 4, 2, 3, 2, 2, 4]
def baseStart_1716207 : Nat := 118140960795 + 1716207 * 2 ^ 59
def prefixEnd_1716207 : Nat := 4983230072969 + 3 ^ 40 * 1716207 * 2
def baseEnd_1716207 : Nat := 587492729073914710613209

theorem tailTrace_1716207 : CollatzResearch.WordTrace tailWord_1716207 prefixEnd_1716207 587492729073914710613209 := by
  unfold tailWord_1716207
  simp only [CollatzResearch.WordTrace]
  refine ⟨62595211693482618665442875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41730141128988412443628583 62595211693482618665442875)
  ·
    refine ⟨93892817540223927998164313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62595211693482618665442875 93892817540223927998164313)
    ·
      refine ⟨70419613155167945998623235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93892817540223927998164313 70419613155167945998623235)
      ·
        refine ⟨105629419732751918997934853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70419613155167945998623235 105629419732751918997934853)
        ·
          refine ⟨19805516199890984812112785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105629419732751918997934853 19805516199890984812112785)
          ·
            refine ⟨14854137149918238609084589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19805516199890984812112785 14854137149918238609084589)
            ·
              refine ⟨5570301431219339478406721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14854137149918238609084589 5570301431219339478406721)
              ·
                refine ⟨4177726073414504608805041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5570301431219339478406721 4177726073414504608805041)
                ·
                  refine ⟨3133294555060878456603781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4177726073414504608805041 3133294555060878456603781)
                  ·
                    refine ⟨587492729073914710613209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133294555060878456603781 587492729073914710613209)
                    ·
                      rfl

theorem cell22_1716207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 2, 4].length) (baseStart_1716207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716207 prefixEnd_1716207 := by exact prefixLift 1716207
  have htrace : WordTrace (prefixWord ++ tailWord_1716207) baseStart_1716207 baseEnd_1716207 := by
    simpa [prefixWord, tailWord_1716207, baseEnd_1716207] using wordTrace_append hprefix tailTrace_1716207
  have hstable : (prefixWord ++ tailWord_1716207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716207).length < 2 ^ (prefixWord ++ tailWord_1716207).sum := by decide
  have hdescent : baseEnd_1716207 < baseStart_1716207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716230 : List Nat := [6, 2, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_1716230 : Nat := 118140960795 + 1716230 * 2 ^ 59
def prefixEnd_1716230 : Nat := 4983230072969 + 3 ^ 40 * 1716230 * 2
def baseEnd_1716230 : Nat := 587500602443950317288139

theorem tailTrace_1716230 : CollatzResearch.WordTrace tailWord_1716230 prefixEnd_1716230 587500602443950317288139 := by
  unfold tailWord_1716230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1956126580387477924797817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41730700381599529062353429 1956126580387477924797817)
  ·
    refine ⟨1467094935290608443598363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1956126580387477924797817 1467094935290608443598363)
    ·
      refine ⟨2200642402935912665397545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1467094935290608443598363 2200642402935912665397545)
      ·
        refine ⟨1650481802201934499048159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2200642402935912665397545 1650481802201934499048159)
        ·
          refine ⟨2475722703302901748572239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1650481802201934499048159 2475722703302901748572239)
          ·
            refine ⟨3713584054954352622858359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475722703302901748572239 3713584054954352622858359)
            ·
              refine ⟨5570376082431528934287539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3713584054954352622858359 5570376082431528934287539)
              ·
                refine ⟨8355564123647293401431309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5570376082431528934287539 8355564123647293401431309)
                ·
                  refine ⟨3133336546367735025536741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8355564123647293401431309 3133336546367735025536741)
                  ·
                    refine ⟨587500602443950317288139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133336546367735025536741 587500602443950317288139)
                    ·
                      rfl

theorem cell22_1716230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_1716230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716230 prefixEnd_1716230 := by exact prefixLift 1716230
  have htrace : WordTrace (prefixWord ++ tailWord_1716230) baseStart_1716230 baseEnd_1716230 := by
    simpa [prefixWord, tailWord_1716230, baseEnd_1716230] using wordTrace_append hprefix tailTrace_1716230
  have hstable : (prefixWord ++ tailWord_1716230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716230).length < 2 ^ (prefixWord ++ tailWord_1716230).sum := by decide
  have hdescent : baseEnd_1716230 < baseStart_1716230 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716297 : List Nat := [1, 2, 1, 1, 2, 2, 3, 3, 3, 4]
def baseStart_1716297 : Nat := 118140960795 + 1716297 * 2 ^ 59
def prefixEnd_1716297 : Nat := 4983230072969 + 3 ^ 40 * 1716297 * 2
def baseEnd_1716297 : Nat := 587523537913184475862933

theorem tailTrace_1716297 : CollatzResearch.WordTrace tailWord_1716297 prefixEnd_1716297 587523537913184475862933 := by
  unfold tailWord_1716297
  simp only [CollatzResearch.WordTrace]
  refine ⟨62598494263156564036219145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41732329508771042690812763 62598494263156564036219145)
  ·
    refine ⟨46948870697367423027164359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62598494263156564036219145 46948870697367423027164359)
    ·
      refine ⟨70423306046051134540746539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46948870697367423027164359 70423306046051134540746539)
      ·
        refine ⟨105634959069076701811119809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70423306046051134540746539 105634959069076701811119809)
        ·
          refine ⟨79226219301807526358339857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105634959069076701811119809 79226219301807526358339857)
          ·
            refine ⟨59419664476355644768754893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79226219301807526358339857 59419664476355644768754893)
            ·
              refine ⟨22282374178633366788283085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59419664476355644768754893 22282374178633366788283085)
              ·
                refine ⟨8355890316987512545606157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22282374178633366788283085 8355890316987512545606157)
                ·
                  refine ⟨3133458868870317204602309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8355890316987512545606157 3133458868870317204602309)
                  ·
                    refine ⟨587523537913184475862933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133458868870317204602309 587523537913184475862933)
                    ·
                      rfl

theorem cell22_1716297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 3, 4].length) (baseStart_1716297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716297 prefixEnd_1716297 := by exact prefixLift 1716297
  have htrace : WordTrace (prefixWord ++ tailWord_1716297) baseStart_1716297 baseEnd_1716297 := by
    simpa [prefixWord, tailWord_1716297, baseEnd_1716297] using wordTrace_append hprefix tailTrace_1716297
  have hstable : (prefixWord ++ tailWord_1716297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716297).length < 2 ^ (prefixWord ++ tailWord_1716297).sum := by decide
  have hdescent : baseEnd_1716297 < baseStart_1716297 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716314 : List Nat := [3, 1, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_1716314 : Nat := 118140960795 + 1716314 * 2 ^ 59
def prefixEnd_1716314 : Nat := 4983230072969 + 3 ^ 40 * 1716314 * 2
def baseEnd_1716314 : Nat := 587529357360602098187881

theorem tailTrace_1716314 : CollatzResearch.WordTrace tailWord_1716314 prefixEnd_1716314 587529357360602098187881 := by
  unfold tailWord_1716314
  simp only [CollatzResearch.WordTrace]
  refine ⟨15649778576023743984896999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41732742869396650626391997 15649778576023743984896999)
  ·
    refine ⟨23474667864035615977345499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15649778576023743984896999 23474667864035615977345499)
    ·
      refine ⟨35212001796053423966018249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23474667864035615977345499 35212001796053423966018249)
      ·
        refine ⟨26409001347040067974513687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35212001796053423966018249 26409001347040067974513687)
        ·
          refine ⟨39613502020560101961770531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26409001347040067974513687 39613502020560101961770531)
          ·
            refine ⟨59420253030840152942655797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39613502020560101961770531 59420253030840152942655797)
            ·
              refine ⟨5570648721641264338373981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59420253030840152942655797 5570648721641264338373981)
              ·
                refine ⟨2088993270615474126890243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5570648721641264338373981 2088993270615474126890243)
                ·
                  refine ⟨3133489905923211190335365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2088993270615474126890243 3133489905923211190335365)
                  ·
                    refine ⟨587529357360602098187881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133489905923211190335365 587529357360602098187881)
                    ·
                      rfl

theorem cell22_1716314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_1716314 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716314 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716314 prefixEnd_1716314 := by exact prefixLift 1716314
  have htrace : WordTrace (prefixWord ++ tailWord_1716314) baseStart_1716314 baseEnd_1716314 := by
    simpa [prefixWord, tailWord_1716314, baseEnd_1716314] using wordTrace_append hprefix tailTrace_1716314
  have hstable : (prefixWord ++ tailWord_1716314).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716314).length < 2 ^ (prefixWord ++ tailWord_1716314).sum := by decide
  have hdescent : baseEnd_1716314 < baseStart_1716314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716318 : List Nat := [4, 4, 1, 1, 2, 1, 1, 1, 7]
def baseStart_1716318 : Nat := 118140960795 + 1716318 * 2 ^ 59
def prefixEnd_1716318 : Nat := 4983230072969 + 3 ^ 40 * 1716318 * 2
def baseEnd_1716318 : Nat := 195843575547449140362623

theorem tailTrace_1716318 : CollatzResearch.WordTrace tailWord_1716318 prefixEnd_1716318 195843575547449140362623 := by
  unfold tailWord_1716318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7824907524510060577841701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41732840130720323081822405 7824907524510060577841701)
  ·
    refine ⟨1467170160845636358345319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7824907524510060577841701 1467170160845636358345319)
    ·
      refine ⟨2200755241268454537517979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1467170160845636358345319 2200755241268454537517979)
      ·
        refine ⟨3301132861902681806276969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2200755241268454537517979 3301132861902681806276969)
        ·
          refine ⟨2475849646427011354707727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3301132861902681806276969 2475849646427011354707727)
          ·
            refine ⟨3713774469640517032061591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475849646427011354707727 3713774469640517032061591)
            ·
              refine ⟨5570661704460775548092387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3713774469640517032061591 5570661704460775548092387)
              ·
                refine ⟨8355992556691163322138581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5570661704460775548092387 8355992556691163322138581)
                ·
                  refine ⟨195843575547449140362623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8355992556691163322138581 195843575547449140362623)
                  ·
                    rfl

theorem cell22_1716318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_1716318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716318 prefixEnd_1716318 := by exact prefixLift 1716318
  have htrace : WordTrace (prefixWord ++ tailWord_1716318) baseStart_1716318 baseEnd_1716318 := by
    simpa [prefixWord, tailWord_1716318, baseEnd_1716318] using wordTrace_append hprefix tailTrace_1716318
  have hstable : (prefixWord ++ tailWord_1716318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716318).length < 2 ^ (prefixWord ++ tailWord_1716318).sum := by decide
  have hdescent : baseEnd_1716318 < baseStart_1716318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716329 : List Nat := [1, 2, 1, 1, 1, 5, 1, 6, 4]
def baseStart_1716329 : Nat := 118140960795 + 1716329 * 2 ^ 59
def prefixEnd_1716329 : Nat := 4983230072969 + 3 ^ 40 * 1716329 * 2
def baseEnd_1716329 : Nat := 195844830722382353020945

theorem tailTrace_1716329 : CollatzResearch.WordTrace tailWord_1716329 prefixEnd_1716329 195844830722382353020945 := by
  unfold tailWord_1716329
  simp only [CollatzResearch.WordTrace]
  refine ⟨62599661399040633501384041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41733107599360422334256027 62599661399040633501384041)
  ·
    refine ⟨46949746049280475126038031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62599661399040633501384041 46949746049280475126038031)
    ·
      refine ⟨70424619073920712689057047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46949746049280475126038031 70424619073920712689057047)
      ·
        refine ⟨105636928610881069033585571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70424619073920712689057047 105636928610881069033585571)
        ·
          refine ⟨158455392916321603550378357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105636928610881069033585571 158455392916321603550378357)
          ·
            refine ⟨14855193085905150332847971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 158455392916321603550378357 14855193085905150332847971)
            ·
              refine ⟨22282789628857725499271957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14855193085905150332847971 22282789628857725499271957)
              ·
                refine ⟨1044505763852705882778373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22282789628857725499271957 1044505763852705882778373)
                ·
                  refine ⟨195844830722382353020945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044505763852705882778373 195844830722382353020945)
                  ·
                    rfl

theorem cell22_1716329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 6, 4].length) (baseStart_1716329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716329 prefixEnd_1716329 := by exact prefixLift 1716329
  have htrace : WordTrace (prefixWord ++ tailWord_1716329) baseStart_1716329 baseEnd_1716329 := by
    simpa [prefixWord, tailWord_1716329, baseEnd_1716329] using wordTrace_append hprefix tailTrace_1716329
  have hstable : (prefixWord ++ tailWord_1716329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716329).length < 2 ^ (prefixWord ++ tailWord_1716329).sum := by decide
  have hdescent : baseEnd_1716329 < baseStart_1716329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716376 : List Nat := [2, 1, 2, 4, 3, 1, 1, 2, 2, 4]
def baseStart_1716376 : Nat := 118140960795 + 1716376 * 2 ^ 59
def prefixEnd_1716376 : Nat := 4983230072969 + 3 ^ 40 * 1716376 * 2
def baseEnd_1716376 : Nat := 587550581227654603137691

theorem tailTrace_1716376 : CollatzResearch.WordTrace tailWord_1716376 prefixEnd_1716376 587550581227654603137691 := by
  unfold tailWord_1716376
  simp only [CollatzResearch.WordTrace]
  refine ⟨31300687814935180264172491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41734250419913573685563321 31300687814935180264172491)
  ·
    refine ⟨46951031722402770396258737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31300687814935180264172491 46951031722402770396258737)
    ·
      refine ⟨35213273791802077797194053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46951031722402770396258737 35213273791802077797194053)
      ·
        refine ⟨6602488835962889586973885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35213273791802077797194053 6602488835962889586973885)
        ·
          refine ⟨2475933313486083595115207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6602488835962889586973885 2475933313486083595115207)
          ·
            refine ⟨3713899970229125392672811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475933313486083595115207 3713899970229125392672811)
            ·
              refine ⟨5570849955343688089009217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3713899970229125392672811 5570849955343688089009217)
              ·
                refine ⟨4178137466507766066756913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5570849955343688089009217 4178137466507766066756913)
                ·
                  refine ⟨3133603099880824550067685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4178137466507766066756913 3133603099880824550067685)
                  ·
                    refine ⟨587550581227654603137691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133603099880824550067685 587550581227654603137691)
                    ·
                      rfl

theorem cell22_1716376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 1, 2, 2, 4].length) (baseStart_1716376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716376 prefixEnd_1716376 := by exact prefixLift 1716376
  have htrace : WordTrace (prefixWord ++ tailWord_1716376) baseStart_1716376 baseEnd_1716376 := by
    simpa [prefixWord, tailWord_1716376, baseEnd_1716376] using wordTrace_append hprefix tailTrace_1716376
  have hstable : (prefixWord ++ tailWord_1716376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716376).length < 2 ^ (prefixWord ++ tailWord_1716376).sum := by decide
  have hdescent : baseEnd_1716376 < baseStart_1716376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716391 : List Nat := [1, 1, 6, 2, 2, 1, 2, 7]
def baseStart_1716391 : Nat := 118140960795 + 1716391 * 2 ^ 59
def prefixEnd_1716391 : Nat := 4983230072969 + 3 ^ 40 * 1716391 * 2
def baseEnd_1716391 : Nat := 65283968448244396001405

theorem tailTrace_1716391 : CollatzResearch.WordTrace tailWord_1716391 prefixEnd_1716391 65283968448244396001405 := by
  unfold tailWord_1716391
  simp only [CollatzResearch.WordTrace]
  refine ⟨62601922724816018090141027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41734615149877345393427351 62601922724816018090141027)
  ·
    refine ⟨93902884087224027135211541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62601922724816018090141027 93902884087224027135211541)
    ·
      refine ⟨4401697691588626271963041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93902884087224027135211541 4401697691588626271963041)
      ·
        refine ⟨3301273268691469703972281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4401697691588626271963041 3301273268691469703972281)
        ·
          refine ⟨2475954951518602277979211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3301273268691469703972281 2475954951518602277979211)
          ·
            refine ⟨3713932427277903416968817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2475954951518602277979211 3713932427277903416968817)
            ·
              refine ⟨2785449320458427562726613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3713932427277903416968817 2785449320458427562726613)
              ·
                refine ⟨65283968448244396001405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2785449320458427562726613 65283968448244396001405)
                ·
                  rfl

theorem cell22_1716391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 2, 7].length) (baseStart_1716391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716391 prefixEnd_1716391 := by exact prefixLift 1716391
  have htrace : WordTrace (prefixWord ++ tailWord_1716391) baseStart_1716391 baseEnd_1716391 := by
    simpa [prefixWord, tailWord_1716391, baseEnd_1716391] using wordTrace_append hprefix tailTrace_1716391
  have hstable : (prefixWord ++ tailWord_1716391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716391).length < 2 ^ (prefixWord ++ tailWord_1716391).sum := by decide
  have hdescent : baseEnd_1716391 < baseStart_1716391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716440 : List Nat := [2, 1, 2, 2, 4, 1, 4, 2, 1, 3]
def baseStart_1716440 : Nat := 118140960795 + 1716440 * 2 ^ 59
def prefixEnd_1716440 : Nat := 4983230072969 + 3 ^ 40 * 1716440 * 2
def baseEnd_1716440 : Nat := 587572489735579769537495

theorem tailTrace_1716440 : CollatzResearch.WordTrace tailWord_1716440 prefixEnd_1716440 587572489735579769537495 := by
  unfold tailWord_1716440
  simp only [CollatzResearch.WordTrace]
  refine ⟨31301854950819249729337387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41735806601092332972449849 31301854950819249729337387)
  ·
    refine ⟨46952782426228874594006081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31301854950819249729337387 46952782426228874594006081)
    ·
      refine ⟨35214586819671655945504561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46952782426228874594006081 35214586819671655945504561)
      ·
        refine ⟨26410940114753741959128421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35214586819671655945504561 26410940114753741959128421)
        ·
          refine ⟨4952051271516326617336579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26410940114753741959128421 4952051271516326617336579)
          ·
            refine ⟨7428076907274489926004869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4952051271516326617336579 7428076907274489926004869)
            ·
              refine ⟨1392764420113966861125913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7428076907274489926004869 1392764420113966861125913)
              ·
                refine ⟨1044573315085475145844435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392764420113966861125913 1044573315085475145844435)
                ·
                  refine ⟨1566859972628212718766653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044573315085475145844435 1566859972628212718766653)
                  ·
                    refine ⟨587572489735579769537495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1566859972628212718766653 587572489735579769537495)
                    ·
                      rfl

theorem cell22_1716440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 4, 2, 1, 3].length) (baseStart_1716440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716440 prefixEnd_1716440 := by exact prefixLift 1716440
  have htrace : WordTrace (prefixWord ++ tailWord_1716440) baseStart_1716440 baseEnd_1716440 := by
    simpa [prefixWord, tailWord_1716440, baseEnd_1716440] using wordTrace_append hprefix tailTrace_1716440
  have hstable : (prefixWord ++ tailWord_1716440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716440).length < 2 ^ (prefixWord ++ tailWord_1716440).sum := by decide
  have hdescent : baseEnd_1716440 < baseStart_1716440 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716449 : List Nat := [1, 2, 3, 1, 3, 1, 1, 1, 5, 4]
def baseStart_1716449 : Nat := 118140960795 + 1716449 * 2 ^ 59
def prefixEnd_1716449 : Nat := 4983230072969 + 3 ^ 40 * 1716449 * 2
def baseEnd_1716449 : Nat := 587575570619506746062467

theorem tailTrace_1716449 : CollatzResearch.WordTrace tailWord_1716449 prefixEnd_1716449 587575570619506746062467 := by
  unfold tailWord_1716449
  simp only [CollatzResearch.WordTrace]
  refine ⟨62604038158605893995752401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41736025439070595997168267 62604038158605893995752401)
  ·
    refine ⟨46953028618954420496814301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62604038158605893995752401 46953028618954420496814301)
    ·
      refine ⟨17607385732107907686305363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46953028618954420496814301 17607385732107907686305363)
      ·
        refine ⟨26411078598161861529458045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17607385732107907686305363 26411078598161861529458045)
        ·
          refine ⟨9904154474310698073546767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26411078598161861529458045 9904154474310698073546767)
          ·
            refine ⟨14856231711466047110320151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9904154474310698073546767 14856231711466047110320151)
            ·
              refine ⟨22284347567199070665480227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14856231711466047110320151 22284347567199070665480227)
              ·
                refine ⟨33426521350798605998220341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22284347567199070665480227 33426521350798605998220341)
                ·
                  refine ⟨3133736376637369312333157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 33426521350798605998220341 3133736376637369312333157)
                  ·
                    refine ⟨587575570619506746062467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133736376637369312333157 587575570619506746062467)
                    ·
                      rfl

theorem cell22_1716449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_1716449 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716449 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716449 prefixEnd_1716449 := by exact prefixLift 1716449
  have htrace : WordTrace (prefixWord ++ tailWord_1716449) baseStart_1716449 baseEnd_1716449 := by
    simpa [prefixWord, tailWord_1716449, baseEnd_1716449] using wordTrace_append hprefix tailTrace_1716449
  have hstable : (prefixWord ++ tailWord_1716449).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716449).length < 2 ^ (prefixWord ++ tailWord_1716449).sum := by decide
  have hdescent : baseEnd_1716449 < baseStart_1716449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716466 : List Nat := [3, 2, 1, 3, 2, 1, 2, 1, 3, 4]
def baseStart_1716466 : Nat := 118140960795 + 1716466 * 2 ^ 59
def prefixEnd_1716466 : Nat := 4983230072969 + 3 ^ 40 * 1716466 * 2
def baseEnd_1716466 : Nat := 587581390066924368387415

theorem tailTrace_1716466 : CollatzResearch.WordTrace tailWord_1716466 prefixEnd_1716466 587581390066924368387415 := by
  unfold tailWord_1716466
  simp only [CollatzResearch.WordTrace]
  refine ⟨15651164549886076474780313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41736438799696203932747501 15651164549886076474780313)
  ·
    refine ⟨11738373412414557356085235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15651164549886076474780313 11738373412414557356085235)
    ·
      refine ⟨17607560118621836034127853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11738373412414557356085235 17607560118621836034127853)
      ·
        refine ⟨6602835044483188512797945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17607560118621836034127853 6602835044483188512797945)
        ·
          refine ⟨4952126283362391384598459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6602835044483188512797945 4952126283362391384598459)
          ·
            refine ⟨7428189425043587076897689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4952126283362391384598459 7428189425043587076897689)
            ·
              refine ⟨5571142068782690307673267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7428189425043587076897689 5571142068782690307673267)
              ·
                refine ⟨8356713103174035461509901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5571142068782690307673267 8356713103174035461509901)
                ·
                  refine ⟨3133767413690263298066213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8356713103174035461509901 3133767413690263298066213)
                  ·
                    refine ⟨587581390066924368387415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3133767413690263298066213 587581390066924368387415)
                    ·
                      rfl

theorem cell22_1716466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_1716466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716466 prefixEnd_1716466 := by exact prefixLift 1716466
  have htrace : WordTrace (prefixWord ++ tailWord_1716466) baseStart_1716466 baseEnd_1716466 := by
    simpa [prefixWord, tailWord_1716466, baseEnd_1716466] using wordTrace_append hprefix tailTrace_1716466
  have hstable : (prefixWord ++ tailWord_1716466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716466).length < 2 ^ (prefixWord ++ tailWord_1716466).sum := by decide
  have hdescent : baseEnd_1716466 < baseStart_1716466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716479 : List Nat := [1, 1, 2, 2, 1, 4, 1, 4, 1, 5]
def baseStart_1716479 : Nat := 118140960795 + 1716479 * 2 ^ 59
def prefixEnd_1716479 : Nat := 4983230072969 + 3 ^ 40 * 1716479 * 2
def baseEnd_1716479 : Nat := 587585840232596667812375

theorem tailTrace_1716479 : CollatzResearch.WordTrace tailWord_1716479 prefixEnd_1716479 587585840232596667812375 := by
  unfold tailWord_1716479
  simp only [CollatzResearch.WordTrace]
  refine ⟨62605132348497209119344491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41736754898998139412896327 62605132348497209119344491)
  ·
    refine ⟨93907698522745813679016737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62605132348497209119344491 93907698522745813679016737)
    ·
      refine ⟨70430773892059360259262553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93907698522745813679016737 70430773892059360259262553)
      ·
        refine ⟨52823080419044520194446915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70430773892059360259262553 52823080419044520194446915)
        ·
          refine ⟨79234620628566780291670373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52823080419044520194446915 79234620628566780291670373)
          ·
            refine ⟨14856491367856271304688195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79234620628566780291670373 14856491367856271304688195)
            ·
              refine ⟨22284737051784406957032293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14856491367856271304688195 22284737051784406957032293)
              ·
                refine ⟨4178388197209576304443555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22284737051784406957032293 4178388197209576304443555)
                ·
                  refine ⟨6267582295814364456665333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178388197209576304443555 6267582295814364456665333)
                  ·
                    refine ⟨587585840232596667812375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6267582295814364456665333 587585840232596667812375)
                    ·
                      rfl

theorem cell22_1716479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 4, 1, 5].length) (baseStart_1716479 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716479 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716479 prefixEnd_1716479 := by exact prefixLift 1716479
  have htrace : WordTrace (prefixWord ++ tailWord_1716479) baseStart_1716479 baseEnd_1716479 := by
    simpa [prefixWord, tailWord_1716479, baseEnd_1716479] using wordTrace_append hprefix tailTrace_1716479
  have hstable : (prefixWord ++ tailWord_1716479).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716479).length < 2 ^ (prefixWord ++ tailWord_1716479).sum := by decide
  have hdescent : baseEnd_1716479 < baseStart_1716479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716569 : List Nat := [1, 2, 1, 2, 2, 2, 1, 3, 1, 7]
def baseStart_1716569 : Nat := 118140960795 + 1716569 * 2 ^ 59
def prefixEnd_1716569 : Nat := 4983230072969 + 3 ^ 40 * 1716569 * 2
def baseEnd_1716569 : Nat := 587616649071866433062099

theorem tailTrace_1716569 : CollatzResearch.WordTrace tailWord_1716569 prefixEnd_1716569 587616649071866433062099 := by
  unfold tailWord_1716569
  simp only [CollatzResearch.WordTrace]
  refine ⟨62608414918171154490120761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41738943278780769660080507 62608414918171154490120761)
  ·
    refine ⟨46956311188628365867590571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62608414918171154490120761 46956311188628365867590571)
    ·
      refine ⟨70434466782942548801385857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46956311188628365867590571 70434466782942548801385857)
      ·
        refine ⟨52825850087206911601039393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70434466782942548801385857 52825850087206911601039393)
        ·
          refine ⟨39619387565405183700779545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52825850087206911601039393 39619387565405183700779545)
          ·
            refine ⟨29714540674053887775584659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39619387565405183700779545 29714540674053887775584659)
            ·
              refine ⟨44571811011080831663376989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29714540674053887775584659 44571811011080831663376989)
              ·
                refine ⟨16714429129155311873766371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44571811011080831663376989 16714429129155311873766371)
                ·
                  refine ⟨25071643693732967810649557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16714429129155311873766371 25071643693732967810649557)
                  ·
                    refine ⟨587616649071866433062099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25071643693732967810649557 587616649071866433062099)
                    ·
                      rfl

theorem cell22_1716569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_1716569 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716569 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716569 prefixEnd_1716569 := by exact prefixLift 1716569
  have htrace : WordTrace (prefixWord ++ tailWord_1716569) baseStart_1716569 baseEnd_1716569 := by
    simpa [prefixWord, tailWord_1716569, baseEnd_1716569] using wordTrace_append hprefix tailTrace_1716569
  have hstable : (prefixWord ++ tailWord_1716569).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716569).length < 2 ^ (prefixWord ++ tailWord_1716569).sum := by decide
  have hdescent : baseEnd_1716569 < baseStart_1716569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716599 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 10]
def baseStart_1716599 : Nat := 118140960795 + 1716599 * 2 ^ 59
def prefixEnd_1716599 : Nat := 4983230072969 + 3 ^ 40 * 1716599 * 2
def baseEnd_1716599 : Nat := 195875639561652118270669

theorem tailTrace_1716599 : CollatzResearch.WordTrace tailWord_1716599 prefixEnd_1716599 195875639561652118270669 := by
  unfold tailWord_1716599
  simp only [CollatzResearch.WordTrace]
  refine ⟨62609509108062469613712851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41739672738708313075808567 62609509108062469613712851)
  ·
    refine ⟨93914263662093704420569277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62609509108062469613712851 93914263662093704420569277)
    ·
      refine ⟨35217848873285139157713479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93914263662093704420569277 35217848873285139157713479)
      ·
        refine ⟨52826773309927708736570219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35217848873285139157713479 52826773309927708736570219)
        ·
          refine ⟨79240159964891563104855329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52826773309927708736570219 79240159964891563104855329)
          ·
            refine ⟨59430119973668672328641497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79240159964891563104855329 59430119973668672328641497)
            ·
              refine ⟨44572589980251504246481123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59430119973668672328641497 44572589980251504246481123)
              ·
                refine ⟨66858884970377256369721685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44572589980251504246481123 66858884970377256369721685)
                ·
                  refine ⟨195875639561652118270669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 66858884970377256369721685 195875639561652118270669)
                  ·
                    rfl

theorem cell22_1716599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 10].length) (baseStart_1716599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716599 prefixEnd_1716599 := by exact prefixLift 1716599
  have htrace : WordTrace (prefixWord ++ tailWord_1716599) baseStart_1716599 baseEnd_1716599 := by
    simpa [prefixWord, tailWord_1716599, baseEnd_1716599] using wordTrace_append hprefix tailTrace_1716599
  have hstable : (prefixWord ++ tailWord_1716599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716599).length < 2 ^ (prefixWord ++ tailWord_1716599).sum := by decide
  have hdescent : baseEnd_1716599 < baseStart_1716599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716609 : List Nat := [1, 2, 4, 3, 1, 3, 2, 2, 1, 3]
def baseStart_1716609 : Nat := 118140960795 + 1716609 * 2 ^ 59
def prefixEnd_1716609 : Nat := 4983230072969 + 3 ^ 40 * 1716609 * 2
def baseEnd_1716609 : Nat := 587630341889319662061977

theorem tailTrace_1716609 : CollatzResearch.WordTrace tailWord_1716609 prefixEnd_1716609 587630341889319662061977 := by
  unfold tailWord_1716609
  simp only [CollatzResearch.WordTrace]
  refine ⟨62609873838026241321576881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41739915892017494214384587 62609873838026241321576881)
  ·
    refine ⟨46957405378519680991182661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62609873838026241321576881 46957405378519680991182661)
    ·
      refine ⟨8804513508472440185846749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46957405378519680991182661 8804513508472440185846749)
      ·
        refine ⟨3301692565677165069692531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8804513508472440185846749 3301692565677165069692531)
        ·
          refine ⟨4952538848515747604538797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3301692565677165069692531 4952538848515747604538797)
          ·
            refine ⟨1857202068193405351702049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4952538848515747604538797 1857202068193405351702049)
            ·
              refine ⟨1392901551145054013776537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857202068193405351702049 1392901551145054013776537)
              ·
                refine ⟨1044676163358790510332403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1392901551145054013776537 1044676163358790510332403)
                ·
                  refine ⟨1567014245038185765498605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044676163358790510332403 1567014245038185765498605)
                  ·
                    refine ⟨587630341889319662061977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567014245038185765498605 587630341889319662061977)
                    ·
                      rfl

theorem cell22_1716609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 2, 2, 1, 3].length) (baseStart_1716609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716609 prefixEnd_1716609 := by exact prefixLift 1716609
  have htrace : WordTrace (prefixWord ++ tailWord_1716609) baseStart_1716609 baseEnd_1716609 := by
    simpa [prefixWord, tailWord_1716609, baseEnd_1716609] using wordTrace_append hprefix tailTrace_1716609
  have hstable : (prefixWord ++ tailWord_1716609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716609).length < 2 ^ (prefixWord ++ tailWord_1716609).sum := by decide
  have hdescent : baseEnd_1716609 < baseStart_1716609 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716616 : List Nat := [2, 1, 3, 3, 1, 1, 2, 3, 6]
def baseStart_1716616 : Nat := 118140960795 + 1716616 * 2 ^ 59
def prefixEnd_1716616 : Nat := 4983230072969 + 3 ^ 40 * 1716616 * 2
def baseEnd_1716616 : Nat := 195877579377457992378985

theorem tailTrace_1716616 : CollatzResearch.WordTrace tailWord_1716616 prefixEnd_1716616 195877579377457992378985 := by
  unfold tailWord_1716616
  simp only [CollatzResearch.WordTrace]
  refine ⟨31305064574500440758540851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41740086099333921011387801 31305064574500440758540851)
  ·
    refine ⟨46957596861750661137811277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31305064574500440758540851 46957596861750661137811277)
    ·
      refine ⟨17609098823156497926679229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46957596861750661137811277 17609098823156497926679229)
      ·
        refine ⟨6603412058683686722504711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17609098823156497926679229 6603412058683686722504711)
        ·
          refine ⟨9905118088025530083757067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6603412058683686722504711 9905118088025530083757067)
          ·
            refine ⟨14857677132038295125635601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9905118088025530083757067 14857677132038295125635601)
            ·
              refine ⟨11143257849028721344226701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14857677132038295125635601 11143257849028721344226701)
              ·
                refine ⟨4178721693385770504085013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11143257849028721344226701 4178721693385770504085013)
                ·
                  refine ⟨195877579377457992378985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4178721693385770504085013 195877579377457992378985)
                  ·
                    rfl

theorem cell22_1716616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 2, 3, 6].length) (baseStart_1716616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716616 prefixEnd_1716616 := by exact prefixLift 1716616
  have htrace : WordTrace (prefixWord ++ tailWord_1716616) baseStart_1716616 baseEnd_1716616 := by
    simpa [prefixWord, tailWord_1716616, baseEnd_1716616] using wordTrace_append hprefix tailTrace_1716616
  have hstable : (prefixWord ++ tailWord_1716616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716616).length < 2 ^ (prefixWord ++ tailWord_1716616).sum := by decide
  have hdescent : baseEnd_1716616 < baseStart_1716616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716631 : List Nat := [1, 1, 3, 3, 1, 1, 3, 3, 1, 5]
def baseStart_1716631 : Nat := 118140960795 + 1716631 * 2 ^ 59
def prefixEnd_1716631 : Nat := 4983230072969 + 3 ^ 40 * 1716631 * 2
def baseEnd_1716631 : Nat := 587637872938918938011909

theorem tailTrace_1716631 : CollatzResearch.WordTrace tailWord_1716631 prefixEnd_1716631 587637872938918938011909 := by
  unfold tailWord_1716631
  simp only [CollatzResearch.WordTrace]
  refine ⟨62610676243946539078877747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41740450829297692719251831 62610676243946539078877747)
  ·
    refine ⟨93916014365919808618316621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62610676243946539078877747 93916014365919808618316621)
    ·
      refine ⟨35218505387219928231868733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93916014365919808618316621 35218505387219928231868733)
      ·
        refine ⟨13206939520207473086950775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35218505387219928231868733 13206939520207473086950775)
        ·
          refine ⟨19810409280311209630426163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13206939520207473086950775 19810409280311209630426163)
          ·
            refine ⟨29715613920466814445639245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19810409280311209630426163 29715613920466814445639245)
            ·
              refine ⟨11143355220175055417114717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29715613920466814445639245 11143355220175055417114717)
              ·
                refine ⟨4178758207565645781418019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11143355220175055417114717 4178758207565645781418019)
                ·
                  refine ⟨6268137311348468672127029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4178758207565645781418019 6268137311348468672127029)
                  ·
                    refine ⟨587637872938918938011909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6268137311348468672127029 587637872938918938011909)
                    ·
                      rfl

theorem cell22_1716631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 3, 1, 5].length) (baseStart_1716631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716631 prefixEnd_1716631 := by exact prefixLift 1716631
  have htrace : WordTrace (prefixWord ++ tailWord_1716631) baseStart_1716631 baseEnd_1716631 := by
    simpa [prefixWord, tailWord_1716631, baseEnd_1716631] using wordTrace_append hprefix tailTrace_1716631
  have hstable : (prefixWord ++ tailWord_1716631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716631).length < 2 ^ (prefixWord ++ tailWord_1716631).sum := by decide
  have hdescent : baseEnd_1716631 < baseStart_1716631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716665 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 2, 3]
def baseStart_1716665 : Nat := 118140960795 + 1716665 * 2 ^ 59
def prefixEnd_1716665 : Nat := 4983230072969 + 3 ^ 40 * 1716665 * 2
def baseEnd_1716665 : Nat := 587649511833754182661805

theorem tailTrace_1716665 : CollatzResearch.WordTrace tailWord_1716665 prefixEnd_1716665 587649511833754182661805 := by
  unfold tailWord_1716665
  simp only [CollatzResearch.WordTrace]
  refine ⟨62611916325823362885615449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41741277550548908590410299 62611916325823362885615449)
  ·
    refine ⟨46958937244367522164211587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62611916325823362885615449 46958937244367522164211587)
    ·
      refine ⟨70438405866551283246317381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46958937244367522164211587 70438405866551283246317381)
      ·
        refine ⟨13207201099978365608684509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70438405866551283246317381 13207201099978365608684509)
        ·
          refine ⟨4952700412491887103256691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13207201099978365608684509 4952700412491887103256691)
          ·
            refine ⟨7429050618737830654885037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4952700412491887103256691 7429050618737830654885037)
            ·
              refine ⟨2785893982026686495581889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7429050618737830654885037 2785893982026686495581889)
              ·
                refine ⟨2089420486520014871686417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2785893982026686495581889 2089420486520014871686417)
                ·
                  refine ⟨1567065364890011153764813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2089420486520014871686417 1567065364890011153764813)
                  ·
                    refine ⟨587649511833754182661805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567065364890011153764813 587649511833754182661805)
                    ·
                      rfl

theorem cell22_1716665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 2, 3].length) (baseStart_1716665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716665 prefixEnd_1716665 := by exact prefixLift 1716665
  have htrace : WordTrace (prefixWord ++ tailWord_1716665) baseStart_1716665 baseEnd_1716665 := by
    simpa [prefixWord, tailWord_1716665, baseEnd_1716665] using wordTrace_append hprefix tailTrace_1716665
  have hstable : (prefixWord ++ tailWord_1716665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716665).length < 2 ^ (prefixWord ++ tailWord_1716665).sum := by decide
  have hdescent : baseEnd_1716665 < baseStart_1716665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716740 : List Nat := [2, 3, 2, 3, 1, 2, 1, 3, 5]
def baseStart_1716740 : Nat := 118140960795 + 1716740 * 2 ^ 59
def prefixEnd_1716740 : Nat := 4983230072969 + 3 ^ 40 * 1716740 * 2
def baseEnd_1716740 : Nat := 195891728622159662345525

theorem tailTrace_1716740 : CollatzResearch.WordTrace tailWord_1716740 prefixEnd_1716740 195891728622159662345525 := by
  unfold tailWord_1716740
  simp only [CollatzResearch.WordTrace]
  refine ⟨31307325900275825347297837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41743101200367767129730449 31307325900275825347297837)
  ·
    refine ⟨11740247212603434505236689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31307325900275825347297837 11740247212603434505236689)
    ·
      refine ⟨8805185409452575878927517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11740247212603434505236689 8805185409452575878927517)
      ·
        refine ⟨3301944528544715954597819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8805185409452575878927517 3301944528544715954597819)
        ·
          refine ⟨4952916792817073931896729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3301944528544715954597819 4952916792817073931896729)
          ·
            refine ⟨3714687594612805448922547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4952916792817073931896729 3714687594612805448922547)
            ·
              refine ⟨5572031391919208173383821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3714687594612805448922547 5572031391919208173383821)
              ·
                refine ⟨2089511771969703065018933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5572031391919208173383821 2089511771969703065018933)
                ·
                  refine ⟨195891728622159662345525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2089511771969703065018933 195891728622159662345525)
                  ·
                    rfl

theorem cell22_1716740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 1, 3, 5].length) (baseStart_1716740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716740 prefixEnd_1716740 := by exact prefixLift 1716740
  have htrace : WordTrace (prefixWord ++ tailWord_1716740) baseStart_1716740 baseEnd_1716740 := by
    simpa [prefixWord, tailWord_1716740, baseEnd_1716740] using wordTrace_append hprefix tailTrace_1716740
  have hstable : (prefixWord ++ tailWord_1716740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716740).length < 2 ^ (prefixWord ++ tailWord_1716740).sum := by decide
  have hdescent : baseEnd_1716740 < baseStart_1716740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716753 : List Nat := [1, 2, 2, 1, 1, 2, 2, 6, 1, 4]
def baseStart_1716753 : Nat := 118140960795 + 1716753 * 2 ^ 59
def prefixEnd_1716753 : Nat := 4983230072969 + 3 ^ 40 * 1716753 * 2
def baseEnd_1716753 : Nat := 587679636032151286461535

theorem tailTrace_1716753 : CollatzResearch.WordTrace tailWord_1716753 prefixEnd_1716753 587679636032151286461535 := by
  unfold tailWord_1716753
  simp only [CollatzResearch.WordTrace]
  refine ⟨62615125949504553914818913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41743417299669702609879275 62615125949504553914818913)
  ·
    refine ⟨46961344462128415436114185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62615125949504553914818913 46961344462128415436114185)
    ·
      refine ⟨35221008346596311577085639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46961344462128415436114185 35221008346596311577085639)
      ·
        refine ⟨52831512519894467365628459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35221008346596311577085639 52831512519894467365628459)
        ·
          refine ⟨79247268779841701048442689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52831512519894467365628459 79247268779841701048442689)
          ·
            refine ⟨59435451584881275786332017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79247268779841701048442689 59435451584881275786332017)
            ·
              refine ⟨44576588688660956839749013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59435451584881275786332017 44576588688660956839749013)
              ·
                refine ⟨2089527594780982351863235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44576588688660956839749013 2089527594780982351863235)
                ·
                  refine ⟨3134291392171473527794853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2089527594780982351863235 3134291392171473527794853)
                  ·
                    refine ⟨587679636032151286461535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3134291392171473527794853 587679636032151286461535)
                    ·
                      rfl

theorem cell22_1716753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 4].length) (baseStart_1716753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716753 prefixEnd_1716753 := by exact prefixLift 1716753
  have htrace : WordTrace (prefixWord ++ tailWord_1716753) baseStart_1716753 baseEnd_1716753 := by
    simpa [prefixWord, tailWord_1716753, baseEnd_1716753] using wordTrace_append hprefix tailTrace_1716753
  have hstable : (prefixWord ++ tailWord_1716753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716753).length < 2 ^ (prefixWord ++ tailWord_1716753).sum := by decide
  have hdescent : baseEnd_1716753 < baseStart_1716753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716800 : List Nat := [2, 1, 1, 2, 2, 2, 4, 3, 2, 3]
def baseStart_1716800 : Nat := 118140960795 + 1716800 * 2 ^ 59
def prefixEnd_1716800 : Nat := 4983230072969 + 3 ^ 40 * 1716800 * 2
def baseEnd_1716800 : Nat := 587695725092658830536391

theorem tailTrace_1716800 : CollatzResearch.WordTrace tailWord_1716800 prefixEnd_1716800 587695725092658830536391 := by
  unfold tailWord_1716800
  simp only [CollatzResearch.WordTrace]
  refine ⟨31308420090167140470889927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41744560120222853961186569 31308420090167140470889927)
  ·
    refine ⟨46962630135250710706334891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31308420090167140470889927 46962630135250710706334891)
    ·
      refine ⟨70443945202876066059502337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46962630135250710706334891 70443945202876066059502337)
      ·
        refine ⟨52832958902157049544626753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70443945202876066059502337 52832958902157049544626753)
        ·
          refine ⟨39624719176617787158470065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52832958902157049544626753 39624719176617787158470065)
          ·
            refine ⟨29718539382463340368852549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39624719176617787158470065 29718539382463340368852549)
            ·
              refine ⟨5572226134211876319159853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29718539382463340368852549 5572226134211876319159853)
              ·
                refine ⟨2089584800329453619684945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5572226134211876319159853 2089584800329453619684945)
                ·
                  refine ⟨1567188600247090214763709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2089584800329453619684945 1567188600247090214763709)
                  ·
                    refine ⟨587695725092658830536391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567188600247090214763709 587695725092658830536391)
                    ·
                      rfl

theorem cell22_1716800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 4, 3, 2, 3].length) (baseStart_1716800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716800 prefixEnd_1716800 := by exact prefixLift 1716800
  have htrace : WordTrace (prefixWord ++ tailWord_1716800) baseStart_1716800 baseEnd_1716800 := by
    simpa [prefixWord, tailWord_1716800, baseEnd_1716800] using wordTrace_append hprefix tailTrace_1716800
  have hstable : (prefixWord ++ tailWord_1716800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716800).length < 2 ^ (prefixWord ++ tailWord_1716800).sum := by decide
  have hdescent : baseEnd_1716800 < baseStart_1716800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716834 : List Nat := [3, 3, 2, 3, 1, 1, 1, 1, 4, 3]
def baseStart_1716834 : Nat := 118140960795 + 1716834 * 2 ^ 59
def prefixEnd_1716834 : Nat := 4983230072969 + 3 ^ 40 * 1716834 * 2
def baseEnd_1716834 : Nat := 587707363987494075186287

theorem tailTrace_1716834 : CollatzResearch.WordTrace tailWord_1716834 prefixEnd_1716834 587707363987494075186287 := by
  unfold tailWord_1716834
  simp only [CollatzResearch.WordTrace]
  refine ⟨15654520065552776187129389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41745386841474069832345037 15654520065552776187129389)
  ·
    refine ⟨5870445024582291070173521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15654520065552776187129389 5870445024582291070173521)
    ·
      refine ⟨4402833768436718302630141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5870445024582291070173521 4402833768436718302630141)
      ·
        refine ⟨1651062663163769363486303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4402833768436718302630141 1651062663163769363486303)
        ·
          refine ⟨2476593994745654045229455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1651062663163769363486303 2476593994745654045229455)
          ·
            refine ⟨3714890992118481067844183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476593994745654045229455 3714890992118481067844183)
            ·
              refine ⟨5572336488177721601766275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3714890992118481067844183 5572336488177721601766275)
              ·
                refine ⟨8358504732266582402649413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5572336488177721601766275 8358504732266582402649413)
                ·
                  refine ⟨1567219637299984200496765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8358504732266582402649413 1567219637299984200496765)
                  ·
                    refine ⟨587707363987494075186287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567219637299984200496765 587707363987494075186287)
                    ·
                      rfl

theorem cell22_1716834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 1, 1, 4, 3].length) (baseStart_1716834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716834 prefixEnd_1716834 := by exact prefixLift 1716834
  have htrace : WordTrace (prefixWord ++ tailWord_1716834) baseStart_1716834 baseEnd_1716834 := by
    simpa [prefixWord, tailWord_1716834, baseEnd_1716834] using wordTrace_append hprefix tailTrace_1716834
  have hstable : (prefixWord ++ tailWord_1716834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716834).length < 2 ^ (prefixWord ++ tailWord_1716834).sum := by decide
  have hdescent : baseEnd_1716834 < baseStart_1716834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716896 : List Nat := [2, 1, 1, 4, 4, 1, 3, 2, 1, 3]
def baseStart_1716896 : Nat := 118140960795 + 1716896 * 2 ^ 59
def prefixEnd_1716896 : Nat := 4983230072969 + 3 ^ 40 * 1716896 * 2
def baseEnd_1716896 : Nat := 587728587854546580136097

theorem tailTrace_1716896 : CollatzResearch.WordTrace tailWord_1716896 prefixEnd_1716896 587728587854546580136097 := by
  unfold tailWord_1716896
  simp only [CollatzResearch.WordTrace]
  refine ⟨31310170793993244668637271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41746894391990992891516361 31310170793993244668637271)
  ·
    refine ⟨46965256190989867002955907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31310170793993244668637271 46965256190989867002955907)
    ·
      refine ⟨70447884286484800504433861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46965256190989867002955907 70447884286484800504433861)
      ·
        refine ⟨13208978303715900094581349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70447884286484800504433861 13208978303715900094581349)
        ·
          refine ⟨2476683431946731267734003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13208978303715900094581349 2476683431946731267734003)
          ·
            refine ⟨3715025147920096901601005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2476683431946731267734003 3715025147920096901601005)
            ·
              refine ⟨1393134430470036338100377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3715025147920096901601005 1393134430470036338100377)
              ·
                refine ⟨1044850822852527253575283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393134430470036338100377 1044850822852527253575283)
                ·
                  refine ⟨1567276234278790880362925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1044850822852527253575283 1567276234278790880362925)
                  ·
                    refine ⟨587728587854546580136097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567276234278790880362925 587728587854546580136097)
                    ·
                      rfl

theorem cell22_1716896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 3, 2, 1, 3].length) (baseStart_1716896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716896 prefixEnd_1716896 := by exact prefixLift 1716896
  have htrace : WordTrace (prefixWord ++ tailWord_1716896) baseStart_1716896 baseEnd_1716896 := by
    simpa [prefixWord, tailWord_1716896, baseEnd_1716896] using wordTrace_append hprefix tailTrace_1716896
  have hstable : (prefixWord ++ tailWord_1716896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716896).length < 2 ^ (prefixWord ++ tailWord_1716896).sum := by decide
  have hdescent : baseEnd_1716896 < baseStart_1716896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716909 : List Nat := [1, 5, 2, 1, 1, 4, 2, 1, 5]
def baseStart_1716909 : Nat := 118140960795 + 1716909 * 2 ^ 59
def prefixEnd_1716909 : Nat := 4983230072969 + 3 ^ 40 * 1716909 * 2
def baseEnd_1716909 : Nat := 195911012673406293187019

theorem tailTrace_1716909 : CollatzResearch.WordTrace tailWord_1716909 prefixEnd_1716909 195911012673406293187019 := by
  unfold tailWord_1716909
  simp only [CollatzResearch.WordTrace]
  refine ⟨62620815736939392557497781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41747210491292928371665187 62620815736939392557497781)
  ·
    refine ⟨5870701475338068052265417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62620815736939392557497781 5870701475338068052265417)
    ·
      refine ⟨4403026106503551039199063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5870701475338068052265417 4403026106503551039199063)
      ·
        refine ⟨6604539159755326558798595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4403026106503551039199063 6604539159755326558798595)
        ·
          refine ⟨9906808739632989838197893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6604539159755326558798595 9906808739632989838197893)
          ·
            refine ⟨1857526638681185594662105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9906808739632989838197893 1857526638681185594662105)
            ·
              refine ⟨1393144979010889195996579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1857526638681185594662105 1393144979010889195996579)
              ·
                refine ⟨2089717468516333793994869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393144979010889195996579 2089717468516333793994869)
                ·
                  refine ⟨195911012673406293187019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2089717468516333793994869 195911012673406293187019)
                  ·
                    rfl

theorem cell22_1716909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_1716909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716909 prefixEnd_1716909 := by exact prefixLift 1716909
  have htrace : WordTrace (prefixWord ++ tailWord_1716909) baseStart_1716909 baseEnd_1716909 := by
    simpa [prefixWord, tailWord_1716909, baseEnd_1716909] using wordTrace_append hprefix tailTrace_1716909
  have hstable : (prefixWord ++ tailWord_1716909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716909).length < 2 ^ (prefixWord ++ tailWord_1716909).sum := by decide
  have hdescent : baseEnd_1716909 < baseStart_1716909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716935 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 4, 3]
def baseStart_1716935 : Nat := 118140960795 + 1716935 * 2 ^ 59
def prefixEnd_1716935 : Nat := 4983230072969 + 3 ^ 40 * 1716935 * 2
def baseEnd_1716935 : Nat := 587741938351563478410977

theorem tailTrace_1716935 : CollatzResearch.WordTrace tailWord_1716935 prefixEnd_1716935 587741938351563478410977 := by
  unfold tailWord_1716935
  simp only [CollatzResearch.WordTrace]
  refine ⟨62621764034845198997944259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41747842689896799331962839 62621764034845198997944259)
  ·
    refine ⟨93932646052267798496916389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62621764034845198997944259 93932646052267798496916389)
    ·
      refine ⟨17612371134800212218171823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93932646052267798496916389 17612371134800212218171823)
      ·
        refine ⟨26418556702200318327257735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17612371134800212218171823 26418556702200318327257735)
        ·
          refine ⟨39627835053300477490886603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26418556702200318327257735 39627835053300477490886603)
          ·
            refine ⟨59441752579950716236329905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39627835053300477490886603 59441752579950716236329905)
            ·
              refine ⟨44581314434963037177247429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59441752579950716236329905 44581314434963037177247429)
              ·
                refine ⟨8358996456555569470733893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44581314434963037177247429 8358996456555569470733893)
                ·
                  refine ⟨1567311835604169275762605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8358996456555569470733893 1567311835604169275762605)
                  ·
                    refine ⟨587741938351563478410977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567311835604169275762605 587741938351563478410977)
                    ·
                      rfl

theorem cell22_1716935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_1716935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716935 prefixEnd_1716935 := by exact prefixLift 1716935
  have htrace : WordTrace (prefixWord ++ tailWord_1716935) baseStart_1716935 baseEnd_1716935 := by
    simpa [prefixWord, tailWord_1716935, baseEnd_1716935] using wordTrace_append hprefix tailTrace_1716935
  have hstable : (prefixWord ++ tailWord_1716935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716935).length < 2 ^ (prefixWord ++ tailWord_1716935).sum := by decide
  have hdescent : baseEnd_1716935 < baseStart_1716935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716952 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 2, 3]
def baseStart_1716952 : Nat := 118140960795 + 1716952 * 2 ^ 59
def prefixEnd_1716952 : Nat := 4983230072969 + 3 ^ 40 * 1716952 * 2
def baseEnd_1716952 : Nat := 587747757798981100735925

theorem tailTrace_1716952 : CollatzResearch.WordTrace tailWord_1716952 prefixEnd_1716952 587747757798981100735925 := by
  unfold tailWord_1716952
  simp only [CollatzResearch.WordTrace]
  refine ⟨31311192037891805450656555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41748256050522407267542073 31311192037891805450656555)
  ·
    refine ⟨46966788056837708175984833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31311192037891805450656555 46966788056837708175984833)
    ·
      refine ⟨35225091042628281131988625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46966788056837708175984833 35225091042628281131988625)
      ·
        refine ⟨26418818281971210848991469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35225091042628281131988625 26418818281971210848991469)
        ·
          refine ⟨9907056855739204068371801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26418818281971210848991469 9907056855739204068371801)
          ·
            refine ⟨7430292641804403051278851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9907056855739204068371801 7430292641804403051278851)
            ·
              refine ⟨11145438962706604576918277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7430292641804403051278851 11145438962706604576918277)
              ·
                refine ⟨2089769805507488358172177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11145438962706604576918277 2089769805507488358172177)
                ·
                  refine ⟨1567327354130616268629133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2089769805507488358172177 1567327354130616268629133)
                  ·
                    refine ⟨587747757798981100735925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567327354130616268629133 587747757798981100735925)
                    ·
                      rfl

theorem cell22_1716952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 2, 3].length) (baseStart_1716952 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716952 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716952 prefixEnd_1716952 := by exact prefixLift 1716952
  have htrace : WordTrace (prefixWord ++ tailWord_1716952) baseStart_1716952 baseEnd_1716952 := by
    simpa [prefixWord, tailWord_1716952, baseEnd_1716952] using wordTrace_append hprefix tailTrace_1716952
  have hstable : (prefixWord ++ tailWord_1716952).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716952).length < 2 ^ (prefixWord ++ tailWord_1716952).sum := by decide
  have hdescent : baseEnd_1716952 < baseStart_1716952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716965 : List Nat := [1, 3, 1, 4, 1, 2, 3, 7]
def baseStart_1716965 : Nat := 118140960795 + 1716965 * 2 ^ 59
def prefixEnd_1716965 : Nat := 4983230072969 + 3 ^ 40 * 1716965 * 2
def baseEnd_1716965 : Nat := 65305800884961488906765

theorem tailTrace_1716965 : CollatzResearch.WordTrace tailWord_1716965 prefixEnd_1716965 65305800884961488906765 := by
  unfold tailWord_1716965
  simp only [CollatzResearch.WordTrace]
  refine ⟨62622858224736514121536349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41748572149824342747690899 62622858224736514121536349)
  ·
    refine ⟨23483571834276192795576131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62622858224736514121536349 23483571834276192795576131)
    ·
      refine ⟨35225357751414289193364197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23483571834276192795576131 35225357751414289193364197)
      ·
        refine ⟨6604754578390179223755787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35225357751414289193364197 6604754578390179223755787)
        ·
          refine ⟨9907131867585268835633681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6604754578390179223755787 9907131867585268835633681)
          ·
            refine ⟨7430348900688951626725261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9907131867585268835633681 7430348900688951626725261)
            ·
              refine ⟨2786380837758356860021973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7430348900688951626725261 2786380837758356860021973)
              ·
                refine ⟨65305800884961488906765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2786380837758356860021973 65305800884961488906765)
                ·
                  rfl

theorem cell22_1716965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 3, 7].length) (baseStart_1716965 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716965 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716965 prefixEnd_1716965 := by exact prefixLift 1716965
  have htrace : WordTrace (prefixWord ++ tailWord_1716965) baseStart_1716965 baseEnd_1716965 := by
    simpa [prefixWord, tailWord_1716965, baseEnd_1716965] using wordTrace_append hprefix tailTrace_1716965
  have hstable : (prefixWord ++ tailWord_1716965).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716965).length < 2 ^ (prefixWord ++ tailWord_1716965).sum := by decide
  have hdescent : baseEnd_1716965 < baseStart_1716965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1716982 : List Nat := [5, 1, 1, 1, 1, 2, 5, 6]
def baseStart_1716982 : Nat := 118140960795 + 1716982 * 2 ^ 59
def prefixEnd_1716982 : Nat := 4983230072969 + 3 ^ 40 * 1716982 * 2
def baseEnd_1716982 : Nat := 65306447490230113609537

theorem tailTrace_1716982 : CollatzResearch.WordTrace tailWord_1716982 prefixEnd_1716982 65306447490230113609537 := by
  unfold tailWord_1716982
  simp only [CollatzResearch.WordTrace]
  refine ⟨3913967391604682876556575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41748985510449950683270133 3913967391604682876556575)
  ·
    refine ⟨5870951087407024314834863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3913967391604682876556575 5870951087407024314834863)
    ·
      refine ⟨8806426631110536472252295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5870951087407024314834863 8806426631110536472252295)
      ·
        refine ⟨13209639946665804708378443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8806426631110536472252295 13209639946665804708378443)
        ·
          refine ⟨19814459919998707062567665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13209639946665804708378443 19814459919998707062567665)
          ·
            refine ⟨14860844939999030296925749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19814459919998707062567665 14860844939999030296925749)
            ·
              refine ⟨1393204213124909090336789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14860844939999030296925749 1393204213124909090336789)
              ·
                refine ⟨65306447490230113609537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1393204213124909090336789 65306447490230113609537)
                ·
                  rfl

theorem cell22_1716982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 5, 6].length) (baseStart_1716982 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1716982 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1716982 prefixEnd_1716982 := by exact prefixLift 1716982
  have htrace : WordTrace (prefixWord ++ tailWord_1716982) baseStart_1716982 baseEnd_1716982 := by
    simpa [prefixWord, tailWord_1716982, baseEnd_1716982] using wordTrace_append hprefix tailTrace_1716982
  have hstable : (prefixWord ++ tailWord_1716982).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1716982).length < 2 ^ (prefixWord ++ tailWord_1716982).sum := by decide
  have hdescent : baseEnd_1716982 < baseStart_1716982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1716982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717025 : List Nat := [1, 2, 3, 2, 1, 2, 1, 3, 2, 5]
def baseStart_1717025 : Nat := 118140960795 + 1717025 * 2 ^ 59
def prefixEnd_1717025 : Nat := 4983230072969 + 3 ^ 40 * 1717025 * 2
def baseEnd_1717025 : Nat := 587772747190833243660701

theorem tailTrace_1717025 : CollatzResearch.WordTrace tailWord_1717025 prefixEnd_1717025 587772747190833243660701 := by
  unfold tailWord_1717025
  simp only [CollatzResearch.WordTrace]
  refine ⟨62625046604519144368720529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41750031069679429579147019 62625046604519144368720529)
  ·
    refine ⟨46968784953389358276540397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62625046604519144368720529 46968784953389358276540397)
    ·
      refine ⟨17613294357521009353702649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46968784953389358276540397 17613294357521009353702649)
      ·
        refine ⟨13209970768140757015276987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17613294357521009353702649 13209970768140757015276987)
        ·
          refine ⟨19814956152211135522915481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13209970768140757015276987 19814956152211135522915481)
          ·
            refine ⟨14861217114158351642186611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19814956152211135522915481 14861217114158351642186611)
            ·
              refine ⟨22291825671237527463279917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14861217114158351642186611 22291825671237527463279917)
              ·
                refine ⟨8359434626714072798729969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22291825671237527463279917 8359434626714072798729969)
                ·
                  refine ⟨6269575970035554599047477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8359434626714072798729969 6269575970035554599047477)
                  ·
                    refine ⟨587772747190833243660701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6269575970035554599047477 587772747190833243660701)
                    ·
                      rfl

theorem cell22_1717025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_1717025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717025 prefixEnd_1717025 := by exact prefixLift 1717025
  have htrace : WordTrace (prefixWord ++ tailWord_1717025) baseStart_1717025 baseEnd_1717025 := by
    simpa [prefixWord, tailWord_1717025, baseEnd_1717025] using wordTrace_append hprefix tailTrace_1717025
  have hstable : (prefixWord ++ tailWord_1717025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717025).length < 2 ^ (prefixWord ++ tailWord_1717025).sum := by decide
  have hdescent : baseEnd_1717025 < baseStart_1717025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717040 : List Nat := [2, 1, 1, 1, 2, 2, 1, 5, 3, 4]
def baseStart_1717040 : Nat := 118140960795 + 1717040 * 2 ^ 59
def prefixEnd_1717040 : Nat := 4983230072969 + 3 ^ 40 * 1717040 * 2
def baseEnd_1717040 : Nat := 587777881997378204535655

theorem tailTrace_1717040 : CollatzResearch.WordTrace tailWord_1717040 prefixEnd_1717040 587777881997378204535655 := by
  unfold tailWord_1717040
  simp only [CollatzResearch.WordTrace]
  refine ⟨31312796849732400965258287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41750395799643201287011049 31312796849732400965258287)
  ·
    refine ⟨46969195274598601447887431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31312796849732400965258287 46969195274598601447887431)
    ·
      refine ⟨70453792911897902171831147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46969195274598601447887431 70453792911897902171831147)
      ·
        refine ⟨105680689367846853257746721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70453792911897902171831147 105680689367846853257746721)
        ·
          refine ⟨79260517025885139943310041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105680689367846853257746721 79260517025885139943310041)
          ·
            refine ⟨59445387769413854957482531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79260517025885139943310041 59445387769413854957482531)
            ·
              refine ⟨89168081654120782436223797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59445387769413854957482531 89168081654120782436223797)
              ·
                refine ⟨8359507655073823353395981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 89168081654120782436223797 8359507655073823353395981)
                ·
                  refine ⟨3134815370652683757523493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8359507655073823353395981 3134815370652683757523493)
                  ·
                    refine ⟨587777881997378204535655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3134815370652683757523493 587777881997378204535655)
                    ·
                      rfl

theorem cell22_1717040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_1717040 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717040 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717040 prefixEnd_1717040 := by exact prefixLift 1717040
  have htrace : WordTrace (prefixWord ++ tailWord_1717040) baseStart_1717040 baseEnd_1717040 := by
    simpa [prefixWord, tailWord_1717040, baseEnd_1717040] using wordTrace_append hprefix tailTrace_1717040
  have hstable : (prefixWord ++ tailWord_1717040).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717040).length < 2 ^ (prefixWord ++ tailWord_1717040).sum := by decide
  have hdescent : baseEnd_1717040 < baseStart_1717040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717072 : List Nat := [2, 1, 1, 1, 1, 4, 2, 6, 4]
def baseStart_1717072 : Nat := 118140960795 + 1717072 * 2 ^ 59
def prefixEnd_1717072 : Nat := 4983230072969 + 3 ^ 40 * 1717072 * 2
def baseEnd_1717072 : Nat := 195929612083780262578519

theorem tailTrace_1717072 : CollatzResearch.WordTrace tailWord_1717072 prefixEnd_1717072 195929612083780262578519 := by
  unfold tailWord_1717072
  simp only [CollatzResearch.WordTrace]
  refine ⟨31313380417674435697840735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41751173890232580930454313 31313380417674435697840735)
  ·
    refine ⟨46970070626511653546761103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31313380417674435697840735 46970070626511653546761103)
    ·
      refine ⟨70455105939767480320141655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46970070626511653546761103 70455105939767480320141655)
      ·
        refine ⟨105682658909651220480212483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70455105939767480320141655 105682658909651220480212483)
        ·
          refine ⟨158523988364476830720318725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105682658909651220480212483 158523988364476830720318725)
          ·
            refine ⟨29723247818339405760059761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158523988364476830720318725 29723247818339405760059761)
            ·
              refine ⟨22292435863754554320044821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29723247818339405760059761 22292435863754554320044821)
              ·
                refine ⟨1044957931113494733752101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 22292435863754554320044821 1044957931113494733752101)
                ·
                  refine ⟨195929612083780262578519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1044957931113494733752101 195929612083780262578519)
                  ·
                    rfl

theorem cell22_1717072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 6, 4].length) (baseStart_1717072 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717072 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717072 prefixEnd_1717072 := by exact prefixLift 1717072
  have htrace : WordTrace (prefixWord ++ tailWord_1717072) baseStart_1717072 baseEnd_1717072 := by
    simpa [prefixWord, tailWord_1717072, baseEnd_1717072] using wordTrace_append hprefix tailTrace_1717072
  have hstable : (prefixWord ++ tailWord_1717072).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717072).length < 2 ^ (prefixWord ++ tailWord_1717072).sum := by decide
  have hdescent : baseEnd_1717072 < baseStart_1717072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717100 : List Nat := [2, 2, 1, 1, 4, 1, 1, 10]
def baseStart_1717100 : Nat := 118140960795 + 1717100 * 2 ^ 59
def prefixEnd_1717100 : Nat := 4983230072969 + 3 ^ 40 * 1717100 * 2
def baseEnd_1717100 : Nat := 65310935691506449781719

theorem tailTrace_1717100 : CollatzResearch.WordTrace tailWord_1717100 prefixEnd_1717100 65310935691506449781719 := by
  unfold tailWord_1717100
  simp only [CollatzResearch.WordTrace]
  refine ⟨31313891039623716088850377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41751854719498288118467169 31313891039623716088850377)
  ·
    refine ⟨23485418279717787066637783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31313891039623716088850377 23485418279717787066637783)
    ·
      refine ⟨35228127419576680599956675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23485418279717787066637783 35228127419576680599956675)
      ·
        refine ⟨52842191129365020899935013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35228127419576680599956675 52842191129365020899935013)
        ·
          refine ⟨9907910836755941418737815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52842191129365020899935013 9907910836755941418737815)
          ·
            refine ⟨14861866255133912128106723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9907910836755941418737815 14861866255133912128106723)
            ·
              refine ⟨22292799382700868192160085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14861866255133912128106723 22292799382700868192160085)
              ·
                refine ⟨65310935691506449781719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 22292799382700868192160085 65310935691506449781719)
                ·
                  rfl

theorem cell22_1717100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 10].length) (baseStart_1717100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717100 prefixEnd_1717100 := by exact prefixLift 1717100
  have htrace : WordTrace (prefixWord ++ tailWord_1717100) baseStart_1717100 baseEnd_1717100 := by
    simpa [prefixWord, tailWord_1717100, baseEnd_1717100] using wordTrace_append hprefix tailTrace_1717100
  have hstable : (prefixWord ++ tailWord_1717100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717100).length < 2 ^ (prefixWord ++ tailWord_1717100).sum := by decide
  have hdescent : baseEnd_1717100 < baseStart_1717100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717145 : List Nat := [1, 2, 1, 2, 1, 3, 1, 2, 9]
def baseStart_1717145 : Nat := 118140960795 + 1717145 * 2 ^ 59
def prefixEnd_1717145 : Nat := 4983230072969 + 3 ^ 40 * 1717145 * 2
def baseEnd_1717145 : Nat := 195937941881064310220111

theorem tailTrace_1717145 : CollatzResearch.WordTrace tailWord_1717145 prefixEnd_1717145 195937941881064310220111 := by
  unfold tailWord_1717145
  simp only [CollatzResearch.WordTrace]
  refine ⟨62629423364084404863088889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41752948909389603242059259 62629423364084404863088889)
  ·
    refine ⟨46972067523063303647316667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62629423364084404863088889 46972067523063303647316667)
    ·
      refine ⟨70458101284594955470975001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46972067523063303647316667 70458101284594955470975001)
      ·
        refine ⟨52843575963446216603231251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70458101284594955470975001 52843575963446216603231251)
        ·
          refine ⟨79265363945169324904846877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52843575963446216603231251 79265363945169324904846877)
          ·
            refine ⟨29724511479438496839317579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 79265363945169324904846877 29724511479438496839317579)
            ·
              refine ⟨44586767219157745258976369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29724511479438496839317579 44586767219157745258976369)
              ·
                refine ⟨33440075414368308944232277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44586767219157745258976369 33440075414368308944232277)
                ·
                  refine ⟨195937941881064310220111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33440075414368308944232277 195937941881064310220111)
                  ·
                    rfl

theorem cell22_1717145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 2, 9].length) (baseStart_1717145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717145 prefixEnd_1717145 := by exact prefixLift 1717145
  have htrace : WordTrace (prefixWord ++ tailWord_1717145) baseStart_1717145 baseEnd_1717145 := by
    simpa [prefixWord, tailWord_1717145, baseEnd_1717145] using wordTrace_append hprefix tailTrace_1717145
  have hstable : (prefixWord ++ tailWord_1717145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717145).length < 2 ^ (prefixWord ++ tailWord_1717145).sum := by decide
  have hdescent : baseEnd_1717145 < baseStart_1717145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717149 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 3, 3]
def baseStart_1717149 : Nat := 118140960795 + 1717149 * 2 ^ 59
def prefixEnd_1717149 : Nat := 4983230072969 + 3 ^ 40 * 1717149 * 2
def baseEnd_1717149 : Nat := 587815194924938253560321

theorem tailTrace_1717149 : CollatzResearch.WordTrace tailWord_1717149 prefixEnd_1717149 587815194924938253560321 := by
  unfold tailWord_1717149
  simp only [CollatzResearch.WordTrace]
  refine ⟨62629569256069913546234501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41753046170713275697489667 62629569256069913546234501)
  ·
    refine ⟨11743044235513108789918969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62629569256069913546234501 11743044235513108789918969)
    ·
      refine ⟨8807283176634831592439227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11743044235513108789918969 8807283176634831592439227)
      ·
        refine ⟨13210924764952247388658841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8807283176634831592439227 13210924764952247388658841)
        ·
          refine ⟨9908193573714185541494131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13210924764952247388658841 9908193573714185541494131)
          ·
            refine ⟨14862290360571278312241197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9908193573714185541494131 14862290360571278312241197)
            ·
              refine ⟨5573358885214229367090449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14862290360571278312241197 5573358885214229367090449)
              ·
                refine ⟨4180019163910672025317837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5573358885214229367090449 4180019163910672025317837)
                ·
                  refine ⟨1567507186466502009494189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4180019163910672025317837 1567507186466502009494189)
                  ·
                    refine ⟨587815194924938253560321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567507186466502009494189 587815194924938253560321)
                    ·
                      rfl

theorem cell22_1717149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 3, 3].length) (baseStart_1717149 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717149 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717149 prefixEnd_1717149 := by exact prefixLift 1717149
  have htrace : WordTrace (prefixWord ++ tailWord_1717149) baseStart_1717149 baseEnd_1717149 := by
    simpa [prefixWord, tailWord_1717149, baseEnd_1717149] using wordTrace_append hprefix tailTrace_1717149
  have hstable : (prefixWord ++ tailWord_1717149).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717149).length < 2 ^ (prefixWord ++ tailWord_1717149).sum := by decide
  have hdescent : baseEnd_1717149 < baseStart_1717149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717177 : List Nat := [1, 2, 1, 4, 2, 2, 1, 2, 2, 5]
def baseStart_1717177 : Nat := 118140960795 + 1717177 * 2 ^ 59
def prefixEnd_1717177 : Nat := 4983230072969 + 3 ^ 40 * 1717177 * 2
def baseEnd_1717177 : Nat := 587824779897155513860235

theorem tailTrace_1717177 : CollatzResearch.WordTrace tailWord_1717177 prefixEnd_1717177 587824779897155513860235 := by
  unfold tailWord_1717177
  simp only [CollatzResearch.WordTrace]
  refine ⟨62630590499968474328253785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41753726999978982885502523 62630590499968474328253785)
  ·
    refine ⟨46972942874976355746190339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62630590499968474328253785 46972942874976355746190339)
    ·
      refine ⟨70459414312464533619285509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46972942874976355746190339 70459414312464533619285509)
      ·
        refine ⟨13211140183587100053616033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70459414312464533619285509 13211140183587100053616033)
        ·
          refine ⟨9908355137690325040212025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13211140183587100053616033 9908355137690325040212025)
          ·
            refine ⟨7431266353267743780159019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9908355137690325040212025 7431266353267743780159019)
            ·
              refine ⟨11146899529901615670238529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7431266353267743780159019 11146899529901615670238529)
              ·
                refine ⟨8360174647426211752678897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11146899529901615670238529 8360174647426211752678897)
                ·
                  refine ⟨6270130985569658814509173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8360174647426211752678897 6270130985569658814509173)
                  ·
                    refine ⟨587824779897155513860235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6270130985569658814509173 587824779897155513860235)
                    ·
                      rfl

theorem cell22_1717177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 2, 2, 5].length) (baseStart_1717177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717177 prefixEnd_1717177 := by exact prefixLift 1717177
  have htrace : WordTrace (prefixWord ++ tailWord_1717177) baseStart_1717177 baseEnd_1717177 := by
    simpa [prefixWord, tailWord_1717177, baseEnd_1717177] using wordTrace_append hprefix tailTrace_1717177
  have hstable : (prefixWord ++ tailWord_1717177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717177).length < 2 ^ (prefixWord ++ tailWord_1717177).sum := by decide
  have hdescent : baseEnd_1717177 < baseStart_1717177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717209 : List Nat := [1, 2, 1, 2, 5, 1, 1, 4, 1, 4]
def baseStart_1717209 : Nat := 118140960795 + 1717209 * 2 ^ 59
def prefixEnd_1717209 : Nat := 4983230072969 + 3 ^ 40 * 1717209 * 2
def baseEnd_1717209 : Nat := 587835734151118097060137

theorem tailTrace_1717209 : CollatzResearch.WordTrace tailWord_1717209 prefixEnd_1717209 587835734151118097060137 := by
  unfold tailWord_1717209
  simp only [CollatzResearch.WordTrace]
  refine ⟨62631757635852543793418681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41754505090568362528945787 62631757635852543793418681)
  ·
    refine ⟨46973818226889407845064011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62631757635852543793418681 46973818226889407845064011)
    ·
      refine ⟨70460727340334111767596017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46973818226889407845064011 70460727340334111767596017)
      ·
        refine ⟨52845545505250583825697013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70460727340334111767596017 52845545505250583825697013)
        ·
          refine ⟨4954269891117242233659095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52845545505250583825697013 4954269891117242233659095)
          ·
            refine ⟨7431404836675863350488643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954269891117242233659095 7431404836675863350488643)
            ·
              refine ⟨11147107255013795025732965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7431404836675863350488643 11147107255013795025732965)
              ·
                refine ⟨2090082610315086567324931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11147107255013795025732965 2090082610315086567324931)
                ·
                  refine ⟨3135123915472629850987397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2090082610315086567324931 3135123915472629850987397)
                  ·
                    refine ⟨587835734151118097060137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3135123915472629850987397 587835734151118097060137)
                    ·
                      rfl

theorem cell22_1717209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 4, 1, 4].length) (baseStart_1717209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717209 prefixEnd_1717209 := by exact prefixLift 1717209
  have htrace : WordTrace (prefixWord ++ tailWord_1717209) baseStart_1717209 baseEnd_1717209 := by
    simpa [prefixWord, tailWord_1717209, baseEnd_1717209] using wordTrace_append hprefix tailTrace_1717209
  have hstable : (prefixWord ++ tailWord_1717209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717209).length < 2 ^ (prefixWord ++ tailWord_1717209).sum := by decide
  have hdescent : baseEnd_1717209 < baseStart_1717209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717241 : List Nat := [1, 2, 1, 3, 1, 3, 5, 2, 4]
def baseStart_1717241 : Nat := 118140960795 + 1717241 * 2 ^ 59
def prefixEnd_1717241 : Nat := 4983230072969 + 3 ^ 40 * 1717241 * 2
def baseEnd_1717241 : Nat := 195948896135026893420013

theorem tailTrace_1717241 : CollatzResearch.WordTrace tailWord_1717241 prefixEnd_1717241 195948896135026893420013 := by
  unfold tailWord_1717241
  simp only [CollatzResearch.WordTrace]
  refine ⟨62632924771736613258583577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41755283181157742172389051 62632924771736613258583577)
  ·
    refine ⟨46974693578802459943937683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62632924771736613258583577 46974693578802459943937683)
    ·
      refine ⟨70462040368203689915906525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46974693578802459943937683 70462040368203689915906525)
      ·
        refine ⟨26423265138076383718464947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70462040368203689915906525 26423265138076383718464947)
        ·
          refine ⟨39634897707114575577697421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26423265138076383718464947 39634897707114575577697421)
          ·
            refine ⟨14863086640167965841636533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39634897707114575577697421 14863086640167965841636533)
            ·
              refine ⟨1393414372515746797653425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14863086640167965841636533 1393414372515746797653425)
              ·
                refine ⟨1045060779386810098240069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393414372515746797653425 1045060779386810098240069)
                ·
                  refine ⟨195948896135026893420013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1045060779386810098240069 195948896135026893420013)
                  ·
                    rfl

theorem cell22_1717241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 4].length) (baseStart_1717241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717241 prefixEnd_1717241 := by exact prefixLift 1717241
  have htrace : WordTrace (prefixWord ++ tailWord_1717241) baseStart_1717241 baseEnd_1717241 := by
    simpa [prefixWord, tailWord_1717241, baseEnd_1717241] using wordTrace_append hprefix tailTrace_1717241
  have hstable : (prefixWord ++ tailWord_1717241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717241).length < 2 ^ (prefixWord ++ tailWord_1717241).sum := by decide
  have hdescent : baseEnd_1717241 < baseStart_1717241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717256 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 2, 3]
def baseStart_1717256 : Nat := 118140960795 + 1717256 * 2 ^ 59
def prefixEnd_1717256 : Nat := 4983230072969 + 3 ^ 40 * 1717256 * 2
def baseEnd_1717256 : Nat := 587851823211625641134993

theorem tailTrace_1717256 : CollatzResearch.WordTrace tailWord_1717256 prefixEnd_1717256 587851823211625641134993 := by
  unfold tailWord_1717256
  simp only [CollatzResearch.WordTrace]
  refine ⟨31316735933341135410189811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41755647911121513880253081 31316735933341135410189811)
  ·
    refine ⟨46975103900011703115284717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31316735933341135410189811 46975103900011703115284717)
    ·
      refine ⟨17615663962504388668231769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46975103900011703115284717 17615663962504388668231769)
      ·
        refine ⟨13211747971878291501173827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17615663962504388668231769 13211747971878291501173827)
        ·
          refine ⟨19817621957817437251760741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13211747971878291501173827 19817621957817437251760741)
          ·
            refine ⟨3715804117090769484705139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19817621957817437251760741 3715804117090769484705139)
            ·
              refine ⟨5573706175636154227057709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3715804117090769484705139 5573706175636154227057709)
              ·
                refine ⟨2090139815863557835146641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5573706175636154227057709 2090139815863557835146641)
                ·
                  refine ⟨1567604861897668376359981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2090139815863557835146641 1567604861897668376359981)
                  ·
                    refine ⟨587851823211625641134993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567604861897668376359981 587851823211625641134993)
                    ·
                      rfl

theorem cell22_1717256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 2, 3].length) (baseStart_1717256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717256 prefixEnd_1717256 := by exact prefixLift 1717256
  have htrace : WordTrace (prefixWord ++ tailWord_1717256) baseStart_1717256 baseEnd_1717256 := by
    simpa [prefixWord, tailWord_1717256, baseEnd_1717256] using wordTrace_append hprefix tailTrace_1717256
  have hstable : (prefixWord ++ tailWord_1717256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717256).length < 2 ^ (prefixWord ++ tailWord_1717256).sum := by decide
  have hdescent : baseEnd_1717256 < baseStart_1717256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717271 : List Nat := [1, 1, 3, 5, 1, 2, 2, 1, 2, 4]
def baseStart_1717271 : Nat := 118140960795 + 1717271 * 2 ^ 59
def prefixEnd_1717271 : Nat := 4983230072969 + 3 ^ 40 * 1717271 * 2
def baseEnd_1717271 : Nat := 587856958018170602009947

theorem tailTrace_1717271 : CollatzResearch.WordTrace tailWord_1717271 prefixEnd_1717271 587856958018170602009947 := by
  unfold tailWord_1717271
  simp only [CollatzResearch.WordTrace]
  refine ⟨62634018961627928382175667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41756012641085285588117111 62634018961627928382175667)
  ·
    refine ⟨93951028442441892573263501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62634018961627928382175667 93951028442441892573263501)
    ·
      refine ⟨35231635665915709714973813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93951028442441892573263501 35231635665915709714973813)
      ·
        refine ⟨3302965843679597785778795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35231635665915709714973813 3302965843679597785778795)
        ·
          refine ⟨4954448765519396678668193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3302965843679597785778795 4954448765519396678668193)
          ·
            refine ⟨3715836574139547509001145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4954448765519396678668193 3715836574139547509001145)
            ·
              refine ⟨2786877430604660631750859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3715836574139547509001145 2786877430604660631750859)
              ·
                refine ⟨4180316145906990947626289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2786877430604660631750859 4180316145906990947626289)
                ·
                  refine ⟨3135237109430243210719717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4180316145906990947626289 3135237109430243210719717)
                  ·
                    refine ⟨587856958018170602009947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3135237109430243210719717 587856958018170602009947)
                    ·
                      rfl

theorem cell22_1717271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 2, 1, 2, 4].length) (baseStart_1717271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717271 prefixEnd_1717271 := by exact prefixLift 1717271
  have htrace : WordTrace (prefixWord ++ tailWord_1717271) baseStart_1717271 baseEnd_1717271 := by
    simpa [prefixWord, tailWord_1717271, baseEnd_1717271] using wordTrace_append hprefix tailTrace_1717271
  have hstable : (prefixWord ++ tailWord_1717271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717271).length < 2 ^ (prefixWord ++ tailWord_1717271).sum := by decide
  have hdescent : baseEnd_1717271 < baseStart_1717271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717318 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 5, 3]
def baseStart_1717318 : Nat := 118140960795 + 1717318 * 2 ^ 59
def prefixEnd_1717318 : Nat := 4983230072969 + 3 ^ 40 * 1717318 * 2
def baseEnd_1717318 : Nat := 587873047078678146084803

theorem tailTrace_1717318 : CollatzResearch.WordTrace tailWord_1717318 prefixEnd_1717318 587873047078678146084803 := by
  unfold tailWord_1717318
  simp only [CollatzResearch.WordTrace]
  refine ⟨1957366662264301731535519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41757155461638436939424405 1957366662264301731535519)
  ·
    refine ⟨2936049993396452597303279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1957366662264301731535519 2936049993396452597303279)
    ·
      refine ⟨4404074990094678895954919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2936049993396452597303279 4404074990094678895954919)
      ·
        refine ⟨6606112485142018343932379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4404074990094678895954919 6606112485142018343932379)
        ·
          refine ⟨9909168727713027515898569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6606112485142018343932379 9909168727713027515898569)
          ·
            refine ⟨7431876545784770636923927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9909168727713027515898569 7431876545784770636923927)
            ·
              refine ⟨11147814818677155955385891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7431876545784770636923927 11147814818677155955385891)
              ·
                refine ⟨16721722228015733933078837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11147814818677155955385891 16721722228015733933078837)
                ·
                  refine ⟨1567661458876475056226141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16721722228015733933078837 1567661458876475056226141)
                  ·
                    refine ⟨587873047078678146084803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567661458876475056226141 587873047078678146084803)
                    ·
                      rfl

theorem cell22_1717318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_1717318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717318 prefixEnd_1717318 := by exact prefixLift 1717318
  have htrace : WordTrace (prefixWord ++ tailWord_1717318) baseStart_1717318 baseEnd_1717318 := by
    simpa [prefixWord, tailWord_1717318, baseEnd_1717318] using wordTrace_append hprefix tailTrace_1717318
  have hstable : (prefixWord ++ tailWord_1717318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717318).length < 2 ^ (prefixWord ++ tailWord_1717318).sum := by decide
  have hdescent : baseEnd_1717318 < baseStart_1717318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717346 : List Nat := [3, 3, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1717346 : Nat := 118140960795 + 1717346 * 2 ^ 59
def prefixEnd_1717346 : Nat := 4983230072969 + 3 ^ 40 * 1717346 * 2
def baseEnd_1717346 : Nat := 587882632050895406384717

theorem tailTrace_1717346 : CollatzResearch.WordTrace tailWord_1717346 prefixEnd_1717346 587882632050895406384717 := by
  unfold tailWord_1717346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15659188609089054047788973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41757836290904144127437261 15659188609089054047788973)
  ·
    refine ⟨5872195728408395267920865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15659188609089054047788973 5872195728408395267920865)
    ·
      refine ⟨4404146796306296450940649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5872195728408395267920865 4404146796306296450940649)
      ·
        refine ⟨3303110097229722338205487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4404146796306296450940649 3303110097229722338205487)
        ·
          refine ⟨4954665145844583507308231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3303110097229722338205487 4954665145844583507308231)
          ·
            refine ⟨7431997718766875260962347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954665145844583507308231 7431997718766875260962347)
            ·
              refine ⟨11147996578150312891443521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7431997718766875260962347 11147996578150312891443521)
              ·
                refine ⟨8360997433612734668582641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11147996578150312891443521 8360997433612734668582641)
                ·
                  refine ⟨6270748075209551001436981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8360997433612734668582641 6270748075209551001436981)
                  ·
                    refine ⟨587882632050895406384717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6270748075209551001436981 587882632050895406384717)
                    ·
                      rfl

theorem cell22_1717346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1717346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717346 prefixEnd_1717346 := by exact prefixLift 1717346
  have htrace : WordTrace (prefixWord ++ tailWord_1717346) baseStart_1717346 baseEnd_1717346 := by
    simpa [prefixWord, tailWord_1717346, baseEnd_1717346] using wordTrace_append hprefix tailTrace_1717346
  have hstable : (prefixWord ++ tailWord_1717346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717346).length < 2 ^ (prefixWord ++ tailWord_1717346).sum := by decide
  have hdescent : baseEnd_1717346 < baseStart_1717346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717359 : List Nat := [1, 1, 2, 1, 3, 3, 4, 1, 6]
def baseStart_1717359 : Nat := 118140960795 + 1717359 * 2 ^ 59
def prefixEnd_1717359 : Nat := 4983230072969 + 3 ^ 40 * 1717359 * 2
def baseEnd_1717359 : Nat := 195962360738855901936559

theorem tailTrace_1717359 : CollatzResearch.WordTrace tailWord_1717359 prefixEnd_1717359 195962360738855901936559 := by
  unfold tailWord_1717359
  simp only [CollatzResearch.WordTrace]
  refine ⟨62637228585309119411379131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41758152390206079607586087 62637228585309119411379131)
  ·
    refine ⟨93955842877963679117068697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62637228585309119411379131 93955842877963679117068697)
    ·
      refine ⟨70466882158472759337801523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93955842877963679117068697 70466882158472759337801523)
      ·
        refine ⟨105700323237709139006702285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70466882158472759337801523 105700323237709139006702285)
        ·
          refine ⟨39637621214140927127513357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105700323237709139006702285 39637621214140927127513357)
          ·
            refine ⟨14864107955302847672817509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39637621214140927127513357 14864107955302847672817509)
            ·
              refine ⟨2787020241619283938653283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14864107955302847672817509 2787020241619283938653283)
              ·
                refine ⟨4180530362428925907979925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787020241619283938653283 4180530362428925907979925)
                ·
                  refine ⟨195962360738855901936559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4180530362428925907979925 195962360738855901936559)
                  ·
                    rfl

theorem cell22_1717359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 4, 1, 6].length) (baseStart_1717359 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717359 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717359 prefixEnd_1717359 := by exact prefixLift 1717359
  have htrace : WordTrace (prefixWord ++ tailWord_1717359) baseStart_1717359 baseEnd_1717359 := by
    simpa [prefixWord, tailWord_1717359, baseEnd_1717359] using wordTrace_append hprefix tailTrace_1717359
  have hstable : (prefixWord ++ tailWord_1717359).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717359).length < 2 ^ (prefixWord ++ tailWord_1717359).sum := by decide
  have hdescent : baseEnd_1717359 < baseStart_1717359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717365 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 5]
def baseStart_1717365 : Nat := 118140960795 + 1717365 * 2 ^ 59
def prefixEnd_1717365 : Nat := 4983230072969 + 3 ^ 40 * 1717365 * 2
def baseEnd_1717365 : Nat := 195963045379728563386553

theorem tailTrace_1717365 : CollatzResearch.WordTrace tailWord_1717365 prefixEnd_1717365 195963045379728563386553 := by
  unfold tailWord_1717365
  simp only [CollatzResearch.WordTrace]
  refine ⟨62637447423287382436097549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41758298282191588290731699 62637447423287382436097549)
  ·
    refine ⟨23489042783732768413536581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62637447423287382436097549 23489042783732768413536581)
    ·
      refine ⟨4404195521949894077538109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23489042783732768413536581 4404195521949894077538109)
      ·
        refine ⟨1651573320731210279076791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4404195521949894077538109 1651573320731210279076791)
        ·
          refine ⟨2477359981096815418615187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1651573320731210279076791 2477359981096815418615187)
          ·
            refine ⟨3716039971645223127922781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2477359981096815418615187 3716039971645223127922781)
            ·
              refine ⟨1393514989366958672971043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3716039971645223127922781 1393514989366958672971043)
              ·
                refine ⟨2090272484050438009456565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393514989366958672971043 2090272484050438009456565)
                ·
                  refine ⟨195963045379728563386553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2090272484050438009456565 195963045379728563386553)
                  ·
                    rfl

theorem cell22_1717365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 5].length) (baseStart_1717365 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717365 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717365 prefixEnd_1717365 := by exact prefixLift 1717365
  have htrace : WordTrace (prefixWord ++ tailWord_1717365) baseStart_1717365 baseEnd_1717365 := by
    simpa [prefixWord, tailWord_1717365, baseEnd_1717365] using wordTrace_append hprefix tailTrace_1717365
  have hstable : (prefixWord ++ tailWord_1717365).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717365).length < 2 ^ (prefixWord ++ tailWord_1717365).sum := by decide
  have hdescent : baseEnd_1717365 < baseStart_1717365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717404 : List Nat := [2, 2, 3, 2, 1, 2, 10]
def baseStart_1717404 : Nat := 118140960795 + 1717404 * 2 ^ 59
def prefixEnd_1717404 : Nat := 4983230072969 + 3 ^ 40 * 1717404 * 2
def baseEnd_1717404 : Nat := 21774166171711206979057

theorem tailTrace_1717404 : CollatzResearch.WordTrace tailWord_1717404 prefixEnd_1717404 21774166171711206979057 := by
  unfold tailWord_1717404
  simp only [CollatzResearch.WordTrace]
  refine ⟨31319434935073046048383633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41759246580097394731178177 31319434935073046048383633)
  ·
    refine ⟨23489576201304784536287725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31319434935073046048383633 23489576201304784536287725)
    ·
      refine ⟨8808591075489294201107897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23489576201304784536287725 8808591075489294201107897)
      ·
        refine ⟨6606443306616970650830923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8808591075489294201107897 6606443306616970650830923)
        ·
          refine ⟨9909664959925455976246385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6606443306616970650830923 9909664959925455976246385)
          ·
            refine ⟨7432248719944091982184789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9909664959925455976246385 7432248719944091982184789)
            ·
              refine ⟨21774166171711206979057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 7432248719944091982184789 21774166171711206979057)
              ·
                rfl

theorem cell22_1717404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 10].length) (baseStart_1717404 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717404 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717404 prefixEnd_1717404 := by exact prefixLift 1717404
  have htrace : WordTrace (prefixWord ++ tailWord_1717404) baseStart_1717404 baseEnd_1717404 := by
    simpa [prefixWord, tailWord_1717404, baseEnd_1717404] using wordTrace_append hprefix tailTrace_1717404
  have hstable : (prefixWord ++ tailWord_1717404).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717404).length < 2 ^ (prefixWord ++ tailWord_1717404).sum := by decide
  have hdescent : baseEnd_1717404 < baseStart_1717404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717410 : List Nat := [3, 3, 1, 3, 3, 1, 1, 1, 6]
def baseStart_1717410 : Nat := 118140960795 + 1717410 * 2 ^ 59
def prefixEnd_1717410 : Nat := 4983230072969 + 3 ^ 40 * 1717410 * 2
def baseEnd_1717410 : Nat := 195968180186273524261507

theorem tailTrace_1717410 : CollatzResearch.WordTrace tailWord_1717410 prefixEnd_1717410 195968180186273524261507 := by
  unfold tailWord_1717410
  simp only [CollatzResearch.WordTrace]
  refine ⟨15659772177031088780371421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41759392472082903414323789 15659772177031088780371421)
  ·
    refine ⟨5872414566386658292639283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15659772177031088780371421 5872414566386658292639283)
    ·
      refine ⟨8808621849579987438958925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5872414566386658292639283 8808621849579987438958925)
      ·
        refine ⟨3303233193592495289609597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8808621849579987438958925 3303233193592495289609597)
        ·
          refine ⟨1238712447597185733603599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3303233193592495289609597 1238712447597185733603599)
          ·
            refine ⟨1858068671395778600405399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1238712447597185733603599 1858068671395778600405399)
            ·
              refine ⟨2787103007093667900608099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858068671395778600405399 2787103007093667900608099)
              ·
                refine ⟨4180654510640501850912149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787103007093667900608099 4180654510640501850912149)
                ·
                  refine ⟨195968180186273524261507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4180654510640501850912149 195968180186273524261507)
                  ·
                    rfl

theorem cell22_1717410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 3, 1, 1, 1, 6].length) (baseStart_1717410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717410 prefixEnd_1717410 := by exact prefixLift 1717410
  have htrace : WordTrace (prefixWord ++ tailWord_1717410) baseStart_1717410 baseEnd_1717410 := by
    simpa [prefixWord, tailWord_1717410, baseEnd_1717410] using wordTrace_append hprefix tailTrace_1717410
  have hstable : (prefixWord ++ tailWord_1717410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717410).length < 2 ^ (prefixWord ++ tailWord_1717410).sum := by decide
  have hdescent : baseEnd_1717410 < baseStart_1717410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717425 : List Nat := [1, 2, 2, 5, 1, 1, 4, 1, 2, 3]
def baseStart_1717425 : Nat := 118140960795 + 1717425 * 2 ^ 59
def prefixEnd_1717425 : Nat := 4983230072969 + 3 ^ 40 * 1717425 * 2
def baseEnd_1717425 : Nat := 587909675365365533659475

theorem tailTrace_1717425 : CollatzResearch.WordTrace tailWord_1717425 prefixEnd_1717425 587909675365365533659475 := by
  unfold tailWord_1717425
  simp only [CollatzResearch.WordTrace]
  refine ⟨62639635803070012683281729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41759757202046675122187819 62639635803070012683281729)
  ·
    refine ⟨46979726852302509512461297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62639635803070012683281729 46979726852302509512461297)
    ·
      refine ⟨35234795139226882134345973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46979726852302509512461297 35234795139226882134345973)
      ·
        refine ⟨3303262044302520200094935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35234795139226882134345973 3303262044302520200094935)
        ·
          refine ⟨4954893066453780300142403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3303262044302520200094935 4954893066453780300142403)
          ·
            refine ⟨7432339599680670450213605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4954893066453780300142403 7432339599680670450213605)
            ·
              refine ⟨1393563674940125709415051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7432339599680670450213605 1393563674940125709415051)
              ·
                refine ⟨2090345512410188564122577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1393563674940125709415051 2090345512410188564122577)
                ·
                  refine ⟨1567759134307641423091933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2090345512410188564122577 1567759134307641423091933)
                  ·
                    refine ⟨587909675365365533659475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567759134307641423091933 587909675365365533659475)
                    ·
                      rfl

theorem cell22_1717425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 1, 2, 3].length) (baseStart_1717425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717425 prefixEnd_1717425 := by exact prefixLift 1717425
  have htrace : WordTrace (prefixWord ++ tailWord_1717425) baseStart_1717425 baseEnd_1717425 := by
    simpa [prefixWord, tailWord_1717425, baseEnd_1717425] using wordTrace_append hprefix tailTrace_1717425
  have hstable : (prefixWord ++ tailWord_1717425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717425).length < 2 ^ (prefixWord ++ tailWord_1717425).sum := by decide
  have hdescent : baseEnd_1717425 < baseStart_1717425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717528 : List Nat := [2, 1, 2, 3, 1, 3, 2, 4, 4]
def baseStart_1717528 : Nat := 118140960795 + 1717528 * 2 ^ 59
def prefixEnd_1717528 : Nat := 4983230072969 + 3 ^ 40 * 1717528 * 2
def baseEnd_1717528 : Nat := 195981644790102532778053

theorem tailTrace_1717528 : CollatzResearch.WordTrace tailWord_1717528 prefixEnd_1717528 195981644790102532778053 := by
  unfold tailWord_1717528
  simp only [CollatzResearch.WordTrace]
  refine ⟨31321696260848430637140619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41762261681131240849520825 31321696260848430637140619)
  ·
    refine ⟨46982544391272645955710929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31321696260848430637140619 46982544391272645955710929)
    ·
      refine ⟨35236908293454484466783197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46982544391272645955710929 35236908293454484466783197)
      ·
        refine ⟨13213840610045431675043699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35236908293454484466783197 13213840610045431675043699)
        ·
          refine ⟨19820760915068147512565549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13213840610045431675043699 19820760915068147512565549)
          ·
            refine ⟨7432785343150555317212081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19820760915068147512565549 7432785343150555317212081)
            ·
              refine ⟨5574589007362916487909061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7432785343150555317212081 5574589007362916487909061)
              ·
                refine ⟨1045235438880546841482949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5574589007362916487909061 1045235438880546841482949)
                ·
                  refine ⟨195981644790102532778053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1045235438880546841482949 195981644790102532778053)
                  ·
                    rfl

theorem cell22_1717528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 4].length) (baseStart_1717528 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717528 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717528 prefixEnd_1717528 := by exact prefixLift 1717528
  have htrace : WordTrace (prefixWord ++ tailWord_1717528) baseStart_1717528 baseEnd_1717528 := by
    simpa [prefixWord, tailWord_1717528, baseEnd_1717528] using wordTrace_append hprefix tailTrace_1717528
  have hstable : (prefixWord ++ tailWord_1717528).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717528).length < 2 ^ (prefixWord ++ tailWord_1717528).sum := by decide
  have hdescent : baseEnd_1717528 < baseStart_1717528 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717541 : List Nat := [1, 3, 1, 2, 4, 1, 1, 2, 1, 6]
def baseStart_1717541 : Nat := 118140960795 + 1717541 * 2 ^ 59
def prefixEnd_1717541 : Nat := 4983230072969 + 3 ^ 40 * 1717541 * 2
def baseEnd_1717541 : Nat := 587949384535979897759119

theorem tailTrace_1717541 : CollatzResearch.WordTrace tailWord_1717541 prefixEnd_1717541 587949384535979897759119 := by
  unfold tailWord_1717541
  simp only [CollatzResearch.WordTrace]
  refine ⟨62643866670649764494504477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41762577780433176329669651 62643866670649764494504477)
  ·
    refine ⟨23491450001493661685439179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62643866670649764494504477 23491450001493661685439179)
    ·
      refine ⟨35237175002240492528158769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23491450001493661685439179 35237175002240492528158769)
      ·
        refine ⟨26427881251680369396119077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35237175002240492528158769 26427881251680369396119077)
        ·
          refine ⟨4955227734690069261772327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26427881251680369396119077 4955227734690069261772327)
          ·
            refine ⟨7432841602035103892658491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4955227734690069261772327 7432841602035103892658491)
            ·
              refine ⟨11149262403052655838987737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7432841602035103892658491 11149262403052655838987737)
              ·
                refine ⟨8361946802289491879240803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11149262403052655838987737 8361946802289491879240803)
                ·
                  refine ⟨12542920203434237818861205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8361946802289491879240803 12542920203434237818861205)
                  ·
                    refine ⟨587949384535979897759119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12542920203434237818861205 587949384535979897759119)
                    ·
                      rfl

theorem cell22_1717541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_1717541 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717541 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717541 prefixEnd_1717541 := by exact prefixLift 1717541
  have htrace : WordTrace (prefixWord ++ tailWord_1717541) baseStart_1717541 baseEnd_1717541 := by
    simpa [prefixWord, tailWord_1717541, baseEnd_1717541] using wordTrace_append hprefix tailTrace_1717541
  have hstable : (prefixWord ++ tailWord_1717541).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717541).length < 2 ^ (prefixWord ++ tailWord_1717541).sum := by decide
  have hdescent : baseEnd_1717541 < baseStart_1717541 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717586 : List Nat := [3, 2, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1717586 : Nat := 118140960795 + 1717586 * 2 ^ 59
def prefixEnd_1717586 : Nat := 4983230072969 + 3 ^ 40 * 1717586 * 2
def baseEnd_1717586 : Nat := 587964788955614780383981

theorem tailTrace_1717586 : CollatzResearch.WordTrace tailWord_1717586 prefixEnd_1717586 587964788955614780383981 := by
  unfold tailWord_1717586
  simp only [CollatzResearch.WordTrace]
  refine ⟨15661376988871684294973153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41763671970324491453261741 15661376988871684294973153)
  ·
    refine ⟨11746032741653763221229865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15661376988871684294973153 11746032741653763221229865)
    ·
      refine ⟨8809524556240322415922399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11746032741653763221229865 8809524556240322415922399)
      ·
        refine ⟨13214286834360483623883599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8809524556240322415922399 13214286834360483623883599)
        ·
          refine ⟨19821430251540725435825399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13214286834360483623883599 19821430251540725435825399)
          ·
            refine ⟨29732145377311088153738099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19821430251540725435825399 29732145377311088153738099)
            ·
              refine ⟨44598218065966632230607149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29732145377311088153738099 44598218065966632230607149)
              ·
                refine ⟨16724331774737487086477681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44598218065966632230607149 16724331774737487086477681)
                ·
                  refine ⟨12543248831053115314858261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16724331774737487086477681 12543248831053115314858261)
                  ·
                    refine ⟨587964788955614780383981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12543248831053115314858261 587964788955614780383981)
                    ·
                      rfl

theorem cell22_1717586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1717586 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717586 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717586 prefixEnd_1717586 := by exact prefixLift 1717586
  have htrace : WordTrace (prefixWord ++ tailWord_1717586) baseStart_1717586 baseEnd_1717586 := by
    simpa [prefixWord, tailWord_1717586, baseEnd_1717586] using wordTrace_append hprefix tailTrace_1717586
  have hstable : (prefixWord ++ tailWord_1717586).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717586).length < 2 ^ (prefixWord ++ tailWord_1717586).sum := by decide
  have hdescent : baseEnd_1717586 < baseStart_1717586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717631 : List Nat := [1, 1, 2, 2, 1, 1, 2, 1, 7, 4]
def baseStart_1717631 : Nat := 118140960795 + 1717631 * 2 ^ 59
def prefixEnd_1717631 : Nat := 4983230072969 + 3 ^ 40 * 1717631 * 2
def baseEnd_1717631 : Nat := 587980193375249663008843

theorem tailTrace_1717631 : CollatzResearch.WordTrace tailWord_1717631 prefixEnd_1717631 587980193375249663008843 := by
  unfold tailWord_1717631
  simp only [CollatzResearch.WordTrace]
  refine ⟨62647149240323709865280747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41764766160215806576853831 62647149240323709865280747)
  ·
    refine ⟨93970723860485564797921121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62647149240323709865280747 93970723860485564797921121)
    ·
      refine ⟨70478042895364173598440841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93970723860485564797921121 70478042895364173598440841)
      ·
        refine ⟨52858532171523130198830631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70478042895364173598440841 52858532171523130198830631)
        ·
          refine ⟨79287798257284695298245947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52858532171523130198830631 79287798257284695298245947)
          ·
            refine ⟨118931697385927042947368921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79287798257284695298245947 118931697385927042947368921)
            ·
              refine ⟨89198773039445282210526691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118931697385927042947368921 89198773039445282210526691)
              ·
                refine ⟨133798159559167923315790037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 89198773039445282210526691 133798159559167923315790037)
                ·
                  refine ⟨3135894364667998202713829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 133798159559167923315790037 3135894364667998202713829)
                  ·
                    refine ⟨587980193375249663008843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3135894364667998202713829 587980193375249663008843)
                    ·
                      rfl

theorem cell22_1717631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 1, 7, 4].length) (baseStart_1717631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717631 prefixEnd_1717631 := by exact prefixLift 1717631
  have htrace : WordTrace (prefixWord ++ tailWord_1717631) baseStart_1717631 baseEnd_1717631 := by
    simpa [prefixWord, tailWord_1717631, baseEnd_1717631] using wordTrace_append hprefix tailTrace_1717631
  have hstable : (prefixWord ++ tailWord_1717631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717631).length < 2 ^ (prefixWord ++ tailWord_1717631).sum := by decide
  have hdescent : baseEnd_1717631 < baseStart_1717631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717639 : List Nat := [1, 1, 4, 2, 2, 4, 2, 2, 1, 3]
def baseStart_1717639 : Nat := 118140960795 + 1717639 * 2 ^ 59
def prefixEnd_1717639 : Nat := 4983230072969 + 3 ^ 40 * 1717639 * 2
def baseEnd_1717639 : Nat := 587982931938740308808819

theorem tailTrace_1717639 : CollatzResearch.WordTrace tailWord_1717639 prefixEnd_1717639 587982931938740308808819 := by
  unfold tailWord_1717639
  simp only [CollatzResearch.WordTrace]
  refine ⟨62647441024294727231571971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41764960682863151487714647 62647441024294727231571971)
  ·
    refine ⟨93971161536442090847357957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62647441024294727231571971 93971161536442090847357957)
    ·
      refine ⟨17619592788082892033879617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93971161536442090847357957 17619592788082892033879617)
      ·
        refine ⟨13214694591062169025409713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17619592788082892033879617 13214694591062169025409713)
        ·
          refine ⟨9911020943296626769057285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13214694591062169025409713 9911020943296626769057285)
          ·
            refine ⟨1858316426868117519198241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9911020943296626769057285 1858316426868117519198241)
            ·
              refine ⟨1393737320151088139398681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1858316426868117519198241 1393737320151088139398681)
              ·
                refine ⟨1045302990113316104549011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1393737320151088139398681 1045302990113316104549011)
                ·
                  refine ⟨1567954485169974156823517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1045302990113316104549011 1567954485169974156823517)
                  ·
                    refine ⟨587982931938740308808819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1567954485169974156823517 587982931938740308808819)
                    ·
                      rfl

theorem cell22_1717639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_1717639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717639 prefixEnd_1717639 := by exact prefixLift 1717639
  have htrace : WordTrace (prefixWord ++ tailWord_1717639) baseStart_1717639 baseEnd_1717639 := by
    simpa [prefixWord, tailWord_1717639, baseEnd_1717639] using wordTrace_append hprefix tailTrace_1717639
  have hstable : (prefixWord ++ tailWord_1717639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717639).length < 2 ^ (prefixWord ++ tailWord_1717639).sum := by decide
  have hdescent : baseEnd_1717639 < baseStart_1717639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717663 : List Nat := [1, 1, 2, 5, 1, 3, 1, 2, 6]
def baseStart_1717663 : Nat := 118140960795 + 1717663 * 2 ^ 59
def prefixEnd_1717663 : Nat := 4983230072969 + 3 ^ 40 * 1717663 * 2
def baseEnd_1717663 : Nat := 195997049209737415402915

theorem tailTrace_1717663 : CollatzResearch.WordTrace tailWord_1717663 prefixEnd_1717663 195997049209737415402915 := by
  unfold tailWord_1717663
  simp only [CollatzResearch.WordTrace]
  refine ⟨62648316376207779330445643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41765544250805186220297095 62648316376207779330445643)
  ·
    refine ⟨93972474564311668995668465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62648316376207779330445643 93972474564311668995668465)
    ·
      refine ⟨70479355923233751746751349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93972474564311668995668465 70479355923233751746751349)
      ·
        refine ⟨6607439617803164226257939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70479355923233751746751349 6607439617803164226257939)
        ·
          refine ⟨9911159426704746339386909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6607439617803164226257939 9911159426704746339386909)
          ·
            refine ⟨3716684785014279877270091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9911159426704746339386909 3716684785014279877270091)
            ·
              refine ⟨5575027177521419815905137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716684785014279877270091 5575027177521419815905137)
              ·
                refine ⟨4181270383141064861928853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5575027177521419815905137 4181270383141064861928853)
                ·
                  refine ⟨195997049209737415402915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4181270383141064861928853 195997049209737415402915)
                  ·
                    rfl

theorem cell22_1717663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 1, 2, 6].length) (baseStart_1717663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717663 prefixEnd_1717663 := by exact prefixLift 1717663
  have htrace : WordTrace (prefixWord ++ tailWord_1717663) baseStart_1717663 baseEnd_1717663 := by
    simpa [prefixWord, tailWord_1717663, baseEnd_1717663] using wordTrace_append hprefix tailTrace_1717663
  have hstable : (prefixWord ++ tailWord_1717663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717663).length < 2 ^ (prefixWord ++ tailWord_1717663).sum := by decide
  have hdescent : baseEnd_1717663 < baseStart_1717663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717693 : List Nat := [1, 4, 1, 2, 2, 1, 2, 1, 4, 4]
def baseStart_1717693 : Nat := 118140960795 + 1717693 * 2 ^ 59
def prefixEnd_1717693 : Nat := 4983230072969 + 3 ^ 40 * 1717693 * 2
def baseEnd_1717693 : Nat := 588001417242302167958653

theorem tailTrace_1717693 : CollatzResearch.WordTrace tailWord_1717693 prefixEnd_1717693 588001417242302167958653 := by
  unfold tailWord_1717693
  simp only [CollatzResearch.WordTrace]
  refine ⟨62649410566099094454037733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41766273710732729636025155 62649410566099094454037733)
  ·
    refine ⟨11746764481143580210132075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62649410566099094454037733 11746764481143580210132075)
    ·
      refine ⟨17620146721715370315198113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11746764481143580210132075 17620146721715370315198113)
      ·
        refine ⟨13215110041286527736398585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17620146721715370315198113 13215110041286527736398585)
        ·
          refine ⟨9911332530964895802298939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13215110041286527736398585 9911332530964895802298939)
          ·
            refine ⟨14866998796447343703448409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9911332530964895802298939 14866998796447343703448409)
            ·
              refine ⟨11150249097335507777586307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14866998796447343703448409 11150249097335507777586307)
              ·
                refine ⟨16725373646003261666379461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11150249097335507777586307 16725373646003261666379461)
                ·
                  refine ⟨3136007558625611562446149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16725373646003261666379461 3136007558625611562446149)
                  ·
                    refine ⟨588001417242302167958653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3136007558625611562446149 588001417242302167958653)
                    ·
                      rfl

theorem cell22_1717693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_1717693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717693 prefixEnd_1717693 := by exact prefixLift 1717693
  have htrace : WordTrace (prefixWord ++ tailWord_1717693) baseStart_1717693 baseEnd_1717693 := by
    simpa [prefixWord, tailWord_1717693, baseEnd_1717693] using wordTrace_append hprefix tailTrace_1717693
  have hstable : (prefixWord ++ tailWord_1717693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717693).length < 2 ^ (prefixWord ++ tailWord_1717693).sum := by decide
  have hdescent : baseEnd_1717693 < baseStart_1717693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717725 : List Nat := [1, 4, 3, 1, 1, 2, 4, 6]
def baseStart_1717725 : Nat := 118140960795 + 1717725 * 2 ^ 59
def prefixEnd_1717725 : Nat := 4983230072969 + 3 ^ 40 * 1717725 * 2
def baseEnd_1717725 : Nat := 65334707944029416795395

theorem tailTrace_1717725 : CollatzResearch.WordTrace tailWord_1717725 prefixEnd_1717725 65334707944029416795395 := by
  unfold tailWord_1717725
  simp only [CollatzResearch.WordTrace]
  refine ⟨62650577701983163919202629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41767051801322109279468419 62650577701983163919202629)
  ·
    refine ⟨11746983319121843234850493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62650577701983163919202629 11746983319121843234850493)
    ·
      refine ⟨4405118744670691213068935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11746983319121843234850493 4405118744670691213068935)
      ·
        refine ⟨6607678117006036819603403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4405118744670691213068935 6607678117006036819603403)
        ·
          refine ⟨9911517175509055229405105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6607678117006036819603403 9911517175509055229405105)
          ·
            refine ⟨7433637881631791422053829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9911517175509055229405105 7433637881631791422053829)
            ·
              refine ⟨1393807102805960891635093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7433637881631791422053829 1393807102805960891635093)
              ·
                refine ⟨65334707944029416795395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1393807102805960891635093 65334707944029416795395)
                ·
                  rfl

theorem cell22_1717725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 4, 6].length) (baseStart_1717725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717725 prefixEnd_1717725 := by exact prefixLift 1717725
  have htrace : WordTrace (prefixWord ++ tailWord_1717725) baseStart_1717725 baseEnd_1717725 := by
    simpa [prefixWord, tailWord_1717725, baseEnd_1717725] using wordTrace_append hprefix tailTrace_1717725
  have hstable : (prefixWord ++ tailWord_1717725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717725).length < 2 ^ (prefixWord ++ tailWord_1717725).sum := by decide
  have hdescent : baseEnd_1717725 < baseStart_1717725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717753 : List Nat := [1, 2, 1, 3, 1, 2, 1, 6, 5]
def baseStart_1717753 : Nat := 118140960795 + 1717753 * 2 ^ 59
def prefixEnd_1717753 : Nat := 4983230072969 + 3 ^ 40 * 1717753 * 2
def baseEnd_1717753 : Nat := 196007318822827337152823

theorem tailTrace_1717753 : CollatzResearch.WordTrace tailWord_1717753 prefixEnd_1717753 196007318822827337152823 := by
  unfold tailWord_1717753
  simp only [CollatzResearch.WordTrace]
  refine ⟨62651598945881724701221913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41767732630587816467481275 62651598945881724701221913)
  ·
    refine ⟨46988699209411293525916435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62651598945881724701221913 46988699209411293525916435)
    ·
      refine ⟨70483048814116940288874653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46988699209411293525916435 70483048814116940288874653)
      ·
        refine ⟨26431143305293852608327995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70483048814116940288874653 26431143305293852608327995)
        ·
          refine ⟨39646714957940778912491993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26431143305293852608327995 39646714957940778912491993)
          ·
            refine ⟨29735036218455584184368995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39646714957940778912491993 29735036218455584184368995)
            ·
              refine ⟨44602554327683376276553493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29735036218455584184368995 44602554327683376276553493)
              ·
                refine ⟨2090744734110158262963445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 44602554327683376276553493 2090744734110158262963445)
                ·
                  refine ⟨196007318822827337152823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2090744734110158262963445 196007318822827337152823)
                  ·
                    rfl

theorem cell22_1717753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 6, 5].length) (baseStart_1717753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717753 prefixEnd_1717753 := by exact prefixLift 1717753
  have htrace : WordTrace (prefixWord ++ tailWord_1717753) baseStart_1717753 baseEnd_1717753 := by
    simpa [prefixWord, tailWord_1717753, baseEnd_1717753] using wordTrace_append hprefix tailTrace_1717753
  have hstable : (prefixWord ++ tailWord_1717753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717753).length < 2 ^ (prefixWord ++ tailWord_1717753).sum := by decide
  have hdescent : baseEnd_1717753 < baseStart_1717753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717757 : List Nat := [1, 4, 1, 1, 1, 6, 1, 1, 3, 3]
def baseStart_1717757 : Nat := 118140960795 + 1717757 * 2 ^ 59
def prefixEnd_1717757 : Nat := 4983230072969 + 3 ^ 40 * 1717757 * 2
def baseEnd_1717757 : Nat := 588023325750227334358457

theorem tailTrace_1717757 : CollatzResearch.WordTrace tailWord_1717757 prefixEnd_1717757 588023325750227334358457 := by
  unfold tailWord_1717757
  simp only [CollatzResearch.WordTrace]
  refine ⟨62651744837867233384367525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41767829891911488922911683 62651744837867233384367525)
  ·
    refine ⟨11747202157100106259568911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62651744837867233384367525 11747202157100106259568911)
    ·
      refine ⟨17620803235650159389353367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11747202157100106259568911 17620803235650159389353367)
      ·
        refine ⟨26431204853475239084030051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17620803235650159389353367 26431204853475239084030051)
        ·
          refine ⟨39646807280212858626045077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26431204853475239084030051 39646807280212858626045077)
          ·
            refine ⟨1858444091259977748095863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39646807280212858626045077 1858444091259977748095863)
            ·
              refine ⟨2787666136889966622143795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858444091259977748095863 2787666136889966622143795)
              ·
                refine ⟨4181499205334949933215693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2787666136889966622143795 4181499205334949933215693)
                ·
                  refine ⟨1568062202000606224955885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4181499205334949933215693 1568062202000606224955885)
                  ·
                    refine ⟨588023325750227334358457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1568062202000606224955885 588023325750227334358457)
                    ·
                      rfl

theorem cell22_1717757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_1717757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717757 prefixEnd_1717757 := by exact prefixLift 1717757
  have htrace : WordTrace (prefixWord ++ tailWord_1717757) baseStart_1717757 baseEnd_1717757 := by
    simpa [prefixWord, tailWord_1717757, baseEnd_1717757] using wordTrace_append hprefix tailTrace_1717757
  have hstable : (prefixWord ++ tailWord_1717757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717757).length < 2 ^ (prefixWord ++ tailWord_1717757).sum := by decide
  have hdescent : baseEnd_1717757 < baseStart_1717757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717768 : List Nat := [2, 1, 3, 2, 1, 1, 2, 3, 2, 5]
def baseStart_1717768 : Nat := 118140960795 + 1717768 * 2 ^ 59
def prefixEnd_1717768 : Nat := 4983230072969 + 3 ^ 40 * 1717768 * 2
def baseEnd_1717768 : Nat := 588027091275026972333423

theorem tailTrace_1717768 : CollatzResearch.WordTrace tailWord_1717768 prefixEnd_1717768 588027091275026972333423 := by
  unfold tailWord_1717768
  simp only [CollatzResearch.WordTrace]
  refine ⟨31326073020413691131508979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41768097360551588175345305 31326073020413691131508979)
  ·
    refine ⟨46989109530620536697263469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31326073020413691131508979 46989109530620536697263469)
    ·
      refine ⟨17620916073982701261473801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46989109530620536697263469 17620916073982701261473801)
      ·
        refine ⟨13215687055487025946105351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17620916073982701261473801 13215687055487025946105351)
        ·
          refine ⟨19823530583230538919158027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13215687055487025946105351 19823530583230538919158027)
          ·
            refine ⟨29735295874845808378737041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19823530583230538919158027 29735295874845808378737041)
            ·
              refine ⟨22301471906134356284052781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29735295874845808378737041 22301471906134356284052781)
              ·
                refine ⟨8363051964800383606519793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22301471906134356284052781 8363051964800383606519793)
                ·
                  refine ⟨6272288973600287704889845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8363051964800383606519793 6272288973600287704889845)
                  ·
                    refine ⟨588027091275026972333423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6272288973600287704889845 588027091275026972333423)
                    ·
                      rfl

theorem cell22_1717768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_1717768 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717768 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717768 prefixEnd_1717768 := by exact prefixLift 1717768
  have htrace : WordTrace (prefixWord ++ tailWord_1717768) baseStart_1717768 baseEnd_1717768 := by
    simpa [prefixWord, tailWord_1717768, baseEnd_1717768] using wordTrace_append hprefix tailTrace_1717768
  have hstable : (prefixWord ++ tailWord_1717768).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717768).length < 2 ^ (prefixWord ++ tailWord_1717768).sum := by decide
  have hdescent : baseEnd_1717768 < baseStart_1717768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717770 : List Nat := [3, 1, 2, 2, 2, 3, 1, 3, 5]
def baseStart_1717770 : Nat := 118140960795 + 1717770 * 2 ^ 59
def prefixEnd_1717770 : Nat := 4983230072969 + 3 ^ 40 * 1717770 * 2
def baseEnd_1717770 : Nat := 196009258638633211261139

theorem tailTrace_1717770 : CollatzResearch.WordTrace tailWord_1717770 prefixEnd_1717770 196009258638633211261139 := by
  unfold tailWord_1717770
  simp only [CollatzResearch.WordTrace]
  refine ⟨15663054746705034151147691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41768145991213424403060509 15663054746705034151147691)
  ·
    refine ⟨23494582120057551226721537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15663054746705034151147691 23494582120057551226721537)
    ·
      refine ⟨17620936590043163420041153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23494582120057551226721537 17620936590043163420041153)
      ·
        refine ⟨13215702442532372565030865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17620936590043163420041153 13215702442532372565030865)
        ·
          refine ⟨9911776831899279423773149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13215702442532372565030865 9911776831899279423773149)
          ·
            refine ⟨3716916311962229783914931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9911776831899279423773149 3716916311962229783914931)
            ·
              refine ⟨5575374467943344675872397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3716916311962229783914931 5575374467943344675872397)
              ·
                refine ⟨2090765425478754253452149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5575374467943344675872397 2090765425478754253452149)
                ·
                  refine ⟨196009258638633211261139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2090765425478754253452149 196009258638633211261139)
                  ·
                    rfl

theorem cell22_1717770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 1, 3, 5].length) (baseStart_1717770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717770 prefixEnd_1717770 := by exact prefixLift 1717770
  have htrace : WordTrace (prefixWord ++ tailWord_1717770) baseStart_1717770 baseEnd_1717770 := by
    simpa [prefixWord, tailWord_1717770, baseEnd_1717770] using wordTrace_append hprefix tailTrace_1717770
  have hstable : (prefixWord ++ tailWord_1717770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717770).length < 2 ^ (prefixWord ++ tailWord_1717770).sum := by decide
  have hdescent : baseEnd_1717770 < baseStart_1717770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717864 : List Nat := [2, 1, 4, 3, 1, 1, 3, 2, 2, 3]
def baseStart_1717864 : Nat := 118140960795 + 1717864 * 2 ^ 59
def prefixEnd_1717864 : Nat := 4983230072969 + 3 ^ 40 * 1717864 * 2
def baseEnd_1717864 : Nat := 588059954036914721933129

theorem tailTrace_1717864 : CollatzResearch.WordTrace tailWord_1717864 prefixEnd_1717864 588059954036914721933129 := by
  unfold tailWord_1717864
  simp only [CollatzResearch.WordTrace]
  refine ⟨31327823724239795329256323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41770431632319727105675097 31327823724239795329256323)
  ·
    refine ⟨46991735586359692993884485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31327823724239795329256323 46991735586359692993884485)
    ·
      refine ⟨8810950422442442436353341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46991735586359692993884485 8810950422442442436353341)
      ·
        refine ⟨3304106408415915913632503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8810950422442442436353341 3304106408415915913632503)
        ·
          refine ⟨4956159612623873870448755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3304106408415915913632503 4956159612623873870448755)
          ·
            refine ⟨7434239418935810805673133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4956159612623873870448755 7434239418935810805673133)
            ·
              refine ⟨2787839782100929052127425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7434239418935810805673133 2787839782100929052127425)
              ·
                refine ⟨2090879836575696789095569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2787839782100929052127425 2090879836575696789095569)
                ·
                  refine ⟨1568159877431772591821677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2090879836575696789095569 1568159877431772591821677)
                  ·
                    refine ⟨588059954036914721933129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1568159877431772591821677 588059954036914721933129)
                    ·
                      rfl

theorem cell22_1717864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_1717864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717864 prefixEnd_1717864 := by exact prefixLift 1717864
  have htrace : WordTrace (prefixWord ++ tailWord_1717864) baseStart_1717864 baseEnd_1717864 := by
    simpa [prefixWord, tailWord_1717864, baseEnd_1717864] using wordTrace_append hprefix tailTrace_1717864
  have hstable : (prefixWord ++ tailWord_1717864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717864).length < 2 ^ (prefixWord ++ tailWord_1717864).sum := by decide
  have hdescent : baseEnd_1717864 < baseStart_1717864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717873 : List Nat := [1, 2, 2, 2, 1, 1, 1, 3, 1, 8]
def baseStart_1717873 : Nat := 118140960795 + 1717873 * 2 ^ 59
def prefixEnd_1717873 : Nat := 4983230072969 + 3 ^ 40 * 1717873 * 2
def baseEnd_1717873 : Nat := 588063034920841698458101

theorem tailTrace_1717873 : CollatzResearch.WordTrace tailWord_1717873 prefixEnd_1717873 588063034920841698458101 := by
  unfold tailWord_1717873
  simp only [CollatzResearch.WordTrace]
  refine ⟨62655975705446985195590273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41770650470297990130393515 62655975705446985195590273)
  ·
    refine ⟨46991981779085238896692705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62655975705446985195590273 46991981779085238896692705)
    ·
      refine ⟨35243986334313929172519529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46991981779085238896692705 35243986334313929172519529)
      ·
        refine ⟨26432989750735446879389647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35243986334313929172519529 26432989750735446879389647)
        ·
          refine ⟨39649484626103170319084471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26432989750735446879389647 39649484626103170319084471)
          ·
            refine ⟨59474226939154755478626707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39649484626103170319084471 59474226939154755478626707)
            ·
              refine ⟨89211340408732133217940061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59474226939154755478626707 89211340408732133217940061)
              ·
                refine ⟨33454252653274549956727523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89211340408732133217940061 33454252653274549956727523)
                ·
                  refine ⟨50181378979911824935091285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33454252653274549956727523 50181378979911824935091285)
                  ·
                    refine ⟨588063034920841698458101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 50181378979911824935091285 588063034920841698458101)
                    ·
                      rfl

theorem cell22_1717873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 3, 1, 8].length) (baseStart_1717873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717873 prefixEnd_1717873 := by exact prefixLift 1717873
  have htrace : WordTrace (prefixWord ++ tailWord_1717873) baseStart_1717873 baseEnd_1717873 := by
    simpa [prefixWord, tailWord_1717873, baseEnd_1717873] using wordTrace_append hprefix tailTrace_1717873
  have hstable : (prefixWord ++ tailWord_1717873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717873).length < 2 ^ (prefixWord ++ tailWord_1717873).sum := by decide
  have hdescent : baseEnd_1717873 < baseStart_1717873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717935 : List Nat := [1, 1, 2, 1, 2, 4, 2, 2, 3, 4]
def baseStart_1717935 : Nat := 118140960795 + 1717935 * 2 ^ 59
def prefixEnd_1717935 : Nat := 4983230072969 + 3 ^ 40 * 1717935 * 2
def baseEnd_1717935 : Nat := 588084258787894203407911

theorem tailTrace_1717935 : CollatzResearch.WordTrace tailWord_1717935 prefixEnd_1717935 588084258787894203407911 := by
  unfold tailWord_1717935
  simp only [CollatzResearch.WordTrace]
  refine ⟨62658237031222369784347259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41772158020814913189564839 62658237031222369784347259)
  ·
    refine ⟨93987355546833554676520889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62658237031222369784347259 93987355546833554676520889)
    ·
      refine ⟨70490516660125166007390667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93987355546833554676520889 70490516660125166007390667)
      ·
        refine ⟨105735774990187749011086001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70490516660125166007390667 105735774990187749011086001)
        ·
          refine ⟨79301831242640811758314501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105735774990187749011086001 79301831242640811758314501)
          ·
            refine ⟨14869093357995152204683969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 79301831242640811758314501 14869093357995152204683969)
            ·
              refine ⟨11151820018496364153512977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14869093357995152204683969 11151820018496364153512977)
              ·
                refine ⟨8363865013872273115134733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11151820018496364153512977 8363865013872273115134733)
                ·
                  refine ⟨3136449380202102418175525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8363865013872273115134733 3136449380202102418175525)
                  ·
                    refine ⟨588084258787894203407911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3136449380202102418175525 588084258787894203407911)
                    ·
                      rfl

theorem cell22_1717935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 3, 4].length) (baseStart_1717935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717935 prefixEnd_1717935 := by exact prefixLift 1717935
  have htrace : WordTrace (prefixWord ++ tailWord_1717935) baseStart_1717935 baseEnd_1717935 := by
    simpa [prefixWord, tailWord_1717935, baseEnd_1717935] using wordTrace_append hprefix tailTrace_1717935
  have hstable : (prefixWord ++ tailWord_1717935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717935).length < 2 ^ (prefixWord ++ tailWord_1717935).sum := by decide
  have hdescent : baseEnd_1717935 < baseStart_1717935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717969 : List Nat := [1, 2, 2, 1, 2, 5, 3, 1, 1, 4]
def baseStart_1717969 : Nat := 118140960795 + 1717969 * 2 ^ 59
def prefixEnd_1717969 : Nat := 4983230072969 + 3 ^ 40 * 1717969 * 2
def baseEnd_1717969 : Nat := 588095897682729448057807

theorem tailTrace_1717969 : CollatzResearch.WordTrace tailWord_1717969 prefixEnd_1717969 588095897682729448057807 := by
  unfold tailWord_1717969
  simp only [CollatzResearch.WordTrace]
  refine ⟨62659477113099193591084961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41772984742066129060723307 62659477113099193591084961)
  ·
    refine ⟨46994607834824395193313721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62659477113099193591084961 46994607834824395193313721)
    ·
      refine ⟨35245955876118296394985291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46994607834824395193313721 35245955876118296394985291)
      ·
        refine ⟨52868933814177444592477937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35245955876118296394985291 52868933814177444592477937)
        ·
          refine ⟨39651700360633083444358453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52868933814177444592477937 39651700360633083444358453)
          ·
            refine ⟨3717346908809351572908605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 39651700360633083444358453 3717346908809351572908605)
            ·
              refine ⟨1394005090803506839840727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3717346908809351572908605 1394005090803506839840727)
              ·
                refine ⟨2091007636205260259761091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1394005090803506839840727 2091007636205260259761091)
                ·
                  refine ⟨3136511454307890389641637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091007636205260259761091 3136511454307890389641637)
                  ·
                    refine ⟨588095897682729448057807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3136511454307890389641637 588095897682729448057807)
                    ·
                      rfl

theorem cell22_1717969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 3, 1, 1, 4].length) (baseStart_1717969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717969 prefixEnd_1717969 := by exact prefixLift 1717969
  have htrace : WordTrace (prefixWord ++ tailWord_1717969) baseStart_1717969 baseEnd_1717969 := by
    simpa [prefixWord, tailWord_1717969, baseEnd_1717969] using wordTrace_append hprefix tailTrace_1717969
  have hstable : (prefixWord ++ tailWord_1717969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717969).length < 2 ^ (prefixWord ++ tailWord_1717969).sum := by decide
  have hdescent : baseEnd_1717969 < baseStart_1717969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717984 : List Nat := [2, 1, 1, 3, 1, 2, 6, 2, 4]
def baseStart_1717984 : Nat := 118140960795 + 1717984 * 2 ^ 59
def prefixEnd_1717984 : Nat := 4983230072969 + 3 ^ 40 * 1717984 * 2
def baseEnd_1717984 : Nat := 196033677496424802977587

theorem tailTrace_1717984 : CollatzResearch.WordTrace tailWord_1717984 prefixEnd_1717984 196033677496424802977587 := by
  unfold tailWord_1717984
  simp only [CollatzResearch.WordTrace]
  refine ⟨31330012104022425576440503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41773349472029900768587337 31330012104022425576440503)
  ·
    refine ⟨46995018156033638364660755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31330012104022425576440503 46995018156033638364660755)
    ·
      refine ⟨70492527234050457546991133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46995018156033638364660755 70492527234050457546991133)
      ·
        refine ⟨26434697712768921580121675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70492527234050457546991133 26434697712768921580121675)
        ·
          refine ⟨39652046569153382370182513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26434697712768921580121675 39652046569153382370182513)
          ·
            refine ⟨29739034926865036777636885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39652046569153382370182513 29739034926865036777636885)
            ·
              refine ⟨1394017262196798598951729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29739034926865036777636885 1394017262196798598951729)
              ·
                refine ⟨1045512946647598949213797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394017262196798598951729 1045512946647598949213797)
                ·
                  refine ⟨196033677496424802977587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1045512946647598949213797 196033677496424802977587)
                  ·
                    rfl

theorem cell22_1717984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 6, 2, 4].length) (baseStart_1717984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717984 prefixEnd_1717984 := by exact prefixLift 1717984
  have htrace : WordTrace (prefixWord ++ tailWord_1717984) baseStart_1717984 baseEnd_1717984 := by
    simpa [prefixWord, tailWord_1717984, baseEnd_1717984] using wordTrace_append hprefix tailTrace_1717984
  have hstable : (prefixWord ++ tailWord_1717984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717984).length < 2 ^ (prefixWord ++ tailWord_1717984).sum := by decide
  have hdescent : baseEnd_1717984 < baseStart_1717984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1717995 : List Nat := [1, 1, 1, 1, 2, 4, 5, 7]
def baseStart_1717995 : Nat := 118140960795 + 1717995 * 2 ^ 59
def prefixEnd_1717995 : Nat := 4983230072969 + 3 ^ 40 * 1717995 * 2
def baseEnd_1717995 : Nat := 65344977557119338545303

theorem tailTrace_1717995 : CollatzResearch.WordTrace tailWord_1717995 prefixEnd_1717995 65344977557119338545303 := by
  unfold tailWord_1717995
  simp only [CollatzResearch.WordTrace]
  refine ⟨62660425411005000031531439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41773616940670000021020959 62660425411005000031531439)
  ·
    refine ⟨93990638116507500047297159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62660425411005000031531439 93990638116507500047297159)
    ·
      refine ⟨140985957174761250070945739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93990638116507500047297159 140985957174761250070945739)
      ·
        refine ⟨211478935762141875106418609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140985957174761250070945739 211478935762141875106418609)
        ·
          refine ⟨158609201821606406329813957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 211478935762141875106418609 158609201821606406329813957)
          ·
            refine ⟨29739225341551201186840117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 158609201821606406329813957 29739225341551201186840117)
            ·
              refine ⟨2788052375770425111266261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29739225341551201186840117 2788052375770425111266261)
              ·
                refine ⟨65344977557119338545303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2788052375770425111266261 65344977557119338545303)
                ·
                  rfl

theorem cell22_1717995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 5, 7].length) (baseStart_1717995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1717995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1717995 prefixEnd_1717995 := by exact prefixLift 1717995
  have htrace : WordTrace (prefixWord ++ tailWord_1717995) baseStart_1717995 baseEnd_1717995 := by
    simpa [prefixWord, tailWord_1717995, baseEnd_1717995] using wordTrace_append hprefix tailTrace_1717995
  have hstable : (prefixWord ++ tailWord_1717995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1717995).length < 2 ^ (prefixWord ++ tailWord_1717995).sum := by decide
  have hdescent : baseEnd_1717995 < baseStart_1717995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1717995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718012 : List Nat := [2, 2, 2, 1, 3, 1, 5, 6]
def baseStart_1718012 : Nat := 118140960795 + 1718012 * 2 ^ 59
def prefixEnd_1718012 : Nat := 4983230072969 + 3 ^ 40 * 1718012 * 2
def baseEnd_1718012 : Nat := 65345624162387963248075

theorem tailTrace_1718012 : CollatzResearch.WordTrace tailWord_1718012 prefixEnd_1718012 65345624162387963248075 := by
  unfold tailWord_1718012
  simp only [CollatzResearch.WordTrace]
  refine ⟨31330522725971705967450145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41774030301295607956600193 31330522725971705967450145)
  ·
    refine ⟨23497892044478779475587609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31330522725971705967450145 23497892044478779475587609)
    ·
      refine ⟨17623419033359084606690707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23497892044478779475587609 17623419033359084606690707)
      ·
        refine ⟨26435128550038626910036061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17623419033359084606690707 26435128550038626910036061)
        ·
          refine ⟨9913173206264485091263523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26435128550038626910036061 9913173206264485091263523)
          ·
            refine ⟨14869759809396727636895285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9913173206264485091263523 14869759809396727636895285)
            ·
              refine ⟨1394039982130943215958933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14869759809396727636895285 1394039982130943215958933)
              ·
                refine ⟨65345624162387963248075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1394039982130943215958933 65345624162387963248075)
                ·
                  rfl

theorem cell22_1718012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 5, 6].length) (baseStart_1718012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718012 prefixEnd_1718012 := by exact prefixLift 1718012
  have htrace : WordTrace (prefixWord ++ tailWord_1718012) baseStart_1718012 baseEnd_1718012 := by
    simpa [prefixWord, tailWord_1718012, baseEnd_1718012] using wordTrace_append hprefix tailTrace_1718012
  have hstable : (prefixWord ++ tailWord_1718012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718012).length < 2 ^ (prefixWord ++ tailWord_1718012).sum := by decide
  have hdescent : baseEnd_1718012 < baseStart_1718012 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718014 : List Nat := [4, 2, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1718014 : Nat := 118140960795 + 1718014 * 2 ^ 59
def prefixEnd_1718014 : Nat := 4983230072969 + 3 ^ 40 * 1718014 * 2
def baseEnd_1718014 : Nat := 588111302102364330682669

theorem tailTrace_1718014 : CollatzResearch.WordTrace tailWord_1718014 prefixEnd_1718014 588111302102364330682669 := by
  unfold tailWord_1718014
  simp only [CollatzResearch.WordTrace]
  refine ⟨7832639799742020784559137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41774078931957444184315397 7832639799742020784559137)
  ·
    refine ⟨5874479849806515588419353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7832639799742020784559137 5874479849806515588419353)
    ·
      refine ⟨4405859887354886691314515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5874479849806515588419353 4405859887354886691314515)
      ·
        refine ⟨6608789831032330036971773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4405859887354886691314515 6608789831032330036971773)
        ·
          refine ⟨2478296186637123763864415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6608789831032330036971773 2478296186637123763864415)
          ·
            refine ⟨3717444279955685645796623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2478296186637123763864415 3717444279955685645796623)
            ·
              refine ⟨5576166419933528468694935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3717444279955685645796623 5576166419933528468694935)
              ·
                refine ⟨8364249629900292703042403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5576166419933528468694935 8364249629900292703042403)
                ·
                  refine ⟨12546374444850439054563605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8364249629900292703042403 12546374444850439054563605)
                  ·
                    refine ⟨588111302102364330682669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12546374444850439054563605 588111302102364330682669)
                    ·
                      rfl

theorem cell22_1718014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1718014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718014 prefixEnd_1718014 := by exact prefixLift 1718014
  have htrace : WordTrace (prefixWord ++ tailWord_1718014) baseStart_1718014 baseEnd_1718014 := by
    simpa [prefixWord, tailWord_1718014, baseEnd_1718014] using wordTrace_append hprefix tailTrace_1718014
  have hstable : (prefixWord ++ tailWord_1718014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718014).length < 2 ^ (prefixWord ++ tailWord_1718014).sum := by decide
  have hdescent : baseEnd_1718014 < baseStart_1718014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718044 : List Nat := [2, 2, 3, 1, 1, 2, 4, 1, 3, 3]
def baseStart_1718044 : Nat := 118140960795 + 1718044 * 2 ^ 59
def prefixEnd_1718044 : Nat := 4983230072969 + 3 ^ 40 * 1718044 * 2
def baseEnd_1718044 : Nat := 588121571715454252432577

theorem tailTrace_1718044 : CollatzResearch.WordTrace tailWord_1718044 prefixEnd_1718044 588121571715454252432577 := by
  unfold tailWord_1718044
  simp only [CollatzResearch.WordTrace]
  refine ⟨31331106293913740700032593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41774808391884987600043457 31331106293913740700032593)
  ·
    refine ⟨23498329720435305525024445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31331106293913740700032593 23498329720435305525024445)
    ·
      refine ⟨8811873645163239571884167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23498329720435305525024445 8811873645163239571884167)
      ·
        refine ⟨13217810467744859357826251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8811873645163239571884167 13217810467744859357826251)
        ·
          refine ⟨19826715701617289036739377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13217810467744859357826251 19826715701617289036739377)
          ·
            refine ⟨14870036776212966777554533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19826715701617289036739377 14870036776212966777554533)
            ·
              refine ⟨2788131895539931270791475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14870036776212966777554533 2788131895539931270791475)
              ·
                refine ⟨4182197843309896906187213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2788131895539931270791475 4182197843309896906187213)
                ·
                  refine ⟨1568324191241211339820205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4182197843309896906187213 1568324191241211339820205)
                  ·
                    refine ⟨588121571715454252432577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1568324191241211339820205 588121571715454252432577)
                    ·
                      rfl

theorem cell22_1718044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_1718044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718044 prefixEnd_1718044 := by exact prefixLift 1718044
  have htrace : WordTrace (prefixWord ++ tailWord_1718044) baseStart_1718044 baseEnd_1718044 := by
    simpa [prefixWord, tailWord_1718044, baseEnd_1718044] using wordTrace_append hprefix tailTrace_1718044
  have hstable : (prefixWord ++ tailWord_1718044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718044).length < 2 ^ (prefixWord ++ tailWord_1718044).sum := by decide
  have hdescent : baseEnd_1718044 < baseStart_1718044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718078 : List Nat := [4, 2, 1, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1718078 : Nat := 118140960795 + 1718078 * 2 ^ 59
def prefixEnd_1718078 : Nat := 4983230072969 + 3 ^ 40 * 1718078 * 2
def baseEnd_1718078 : Nat := 588133210610289497082473

theorem tailTrace_1718078 : CollatzResearch.WordTrace tailWord_1718078 prefixEnd_1718078 588133210610289497082473 := by
  unfold tailWord_1718078
  simp only [CollatzResearch.WordTrace]
  refine ⟨7832931583713038150850361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41775635113136203471201925 7832931583713038150850361)
  ·
    refine ⟨5874698687784778613137771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7832931583713038150850361 5874698687784778613137771)
    ·
      refine ⟨8812048031677167919706657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5874698687784778613137771 8812048031677167919706657)
      ·
        refine ⟨6609036023757875939779993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8812048031677167919706657 6609036023757875939779993)
        ·
          refine ⟨4956777017818406954834995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6609036023757875939779993 4956777017818406954834995)
          ·
            refine ⟨7435165526727610432252493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4956777017818406954834995 7435165526727610432252493)
            ·
              refine ⟨2788187072522853912094685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7435165526727610432252493 2788187072522853912094685)
              ·
                refine ⟨1045570152196070217035507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2788187072522853912094685 1045570152196070217035507)
                ·
                  refine ⟨1568355228294105325553261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1045570152196070217035507 1568355228294105325553261)
                  ·
                    refine ⟨588133210610289497082473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1568355228294105325553261 588133210610289497082473)
                    ·
                      rfl

theorem cell22_1718078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1718078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718078 prefixEnd_1718078 := by exact prefixLift 1718078
  have htrace : WordTrace (prefixWord ++ tailWord_1718078) baseStart_1718078 baseEnd_1718078 := by
    simpa [prefixWord, tailWord_1718078, baseEnd_1718078] using wordTrace_append hprefix tailTrace_1718078
  have hstable : (prefixWord ++ tailWord_1718078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718078).length < 2 ^ (prefixWord ++ tailWord_1718078).sum := by decide
  have hdescent : baseEnd_1718078 < baseStart_1718078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718108 : List Nat := [2, 2, 4, 2, 2, 2, 2, 1, 5]
def baseStart_1718108 : Nat := 118140960795 + 1718108 * 2 ^ 59
def prefixEnd_1718108 : Nat := 4983230072969 + 3 ^ 40 * 1718108 * 2
def baseEnd_1718108 : Nat := 196047826741126472944127

theorem tailTrace_1718108 : CollatzResearch.WordTrace tailWord_1718108 prefixEnd_1718108 196047826741126472944127 := by
  unfold tailWord_1718108
  simp only [CollatzResearch.WordTrace]
  refine ⟨31332273429797810165197489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41776364573063746886929985 31332273429797810165197489)
  ·
    refine ⟨23499205072348357623898117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31332273429797810165197489 23499205072348357623898117)
    ·
      refine ⟨4406100951065317054480897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23499205072348357623898117 4406100951065317054480897)
      ·
        refine ⟨3304575713298987790860673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4406100951065317054480897 3304575713298987790860673)
        ·
          refine ⟨2478431784974240843145505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3304575713298987790860673 2478431784974240843145505)
          ·
            refine ⟨1858823838730680632359129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2478431784974240843145505 1858823838730680632359129)
            ·
              refine ⟨1394117879048010474269347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1858823838730680632359129 1394117879048010474269347)
              ·
                refine ⟨2091176818572015711404021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1394117879048010474269347 2091176818572015711404021)
                ·
                  refine ⟨196047826741126472944127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2091176818572015711404021 196047826741126472944127)
                  ·
                    rfl

theorem cell22_1718108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 2, 2, 1, 5].length) (baseStart_1718108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718108 prefixEnd_1718108 := by exact prefixLift 1718108
  have htrace : WordTrace (prefixWord ++ tailWord_1718108) baseStart_1718108 baseEnd_1718108 := by
    simpa [prefixWord, tailWord_1718108, baseEnd_1718108] using wordTrace_append hprefix tailTrace_1718108
  have hstable : (prefixWord ++ tailWord_1718108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718108).length < 2 ^ (prefixWord ++ tailWord_1718108).sum := by decide
  have hdescent : baseEnd_1718108 < baseStart_1718108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718117 : List Nat := [1, 3, 1, 3, 1, 1, 1, 5, 1, 5]
def baseStart_1718117 : Nat := 118140960795 + 1718117 * 2 ^ 59
def prefixEnd_1718117 : Nat := 4983230072969 + 3 ^ 40 * 1718117 * 2
def baseEnd_1718117 : Nat := 588146561107306395357353

theorem tailTrace_1718117 : CollatzResearch.WordTrace tailWord_1718117 prefixEnd_1718117 588146561107306395357353 := by
  unfold tailWord_1718117
  simp only [CollatzResearch.WordTrace]
  refine ⟨62664875116563014867472605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41776583411042009911648403 62664875116563014867472605)
  ·
    refine ⟨23499328168711130575302227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62664875116563014867472605 23499328168711130575302227)
    ·
      refine ⟨35248992253066695862953341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23499328168711130575302227 35248992253066695862953341)
      ·
        refine ⟨13218372094900010948607503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35248992253066695862953341 13218372094900010948607503)
        ·
          refine ⟨19827558142350016422911255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13218372094900010948607503 19827558142350016422911255)
          ·
            refine ⟨29741337213525024634366883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19827558142350016422911255 29741337213525024634366883)
            ·
              refine ⟨44612005820287536951550325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29741337213525024634366883 44612005820287536951550325)
              ·
                refine ⟨4182375545651956589207843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44612005820287536951550325 4182375545651956589207843)
                ·
                  refine ⟨6273563318477934883811765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4182375545651956589207843 6273563318477934883811765)
                  ·
                    refine ⟨588146561107306395357353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6273563318477934883811765 588146561107306395357353)
                    ·
                      rfl

theorem cell22_1718117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 5, 1, 5].length) (baseStart_1718117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718117 prefixEnd_1718117 := by exact prefixLift 1718117
  have htrace : WordTrace (prefixWord ++ tailWord_1718117) baseStart_1718117 baseEnd_1718117 := by
    simpa [prefixWord, tailWord_1718117, baseEnd_1718117] using wordTrace_append hprefix tailTrace_1718117
  have hstable : (prefixWord ++ tailWord_1718117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718117).length < 2 ^ (prefixWord ++ tailWord_1718117).sum := by decide
  have hdescent : baseEnd_1718117 < baseStart_1718117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718164 : List Nat := [2, 4, 2, 1, 1, 2, 3, 7]
def baseStart_1718164 : Nat := 118140960795 + 1718164 * 2 ^ 59
def prefixEnd_1718164 : Nat := 4983230072969 + 3 ^ 40 * 1718164 * 2
def baseEnd_1718164 : Nat := 65351405574201548825801

theorem tailTrace_1718164 : CollatzResearch.WordTrace tailWord_1718164 prefixEnd_1718164 65351405574201548825801 := by
  unfold tailWord_1718164
  simp only [CollatzResearch.WordTrace]
  refine ⟨31333294673696370947216773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41777726231595161262955697 31333294673696370947216773)
  ·
    refine ⟨5874992751318069552603145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31333294673696370947216773 5874992751318069552603145)
    ·
      refine ⟨4406244563488552164452359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5874992751318069552603145 4406244563488552164452359)
      ·
        refine ⟨6609366845232828246678539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4406244563488552164452359 6609366845232828246678539)
        ·
          refine ⟨9914050267849242370017809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6609366845232828246678539 9914050267849242370017809)
          ·
            refine ⟨7435537700886931777513357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9914050267849242370017809 7435537700886931777513357)
            ·
              refine ⟨2788326637832599416567509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7435537700886931777513357 2788326637832599416567509)
              ·
                refine ⟨65351405574201548825801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2788326637832599416567509 65351405574201548825801)
                ·
                  rfl

theorem cell22_1718164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 7].length) (baseStart_1718164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718164 prefixEnd_1718164 := by exact prefixLift 1718164
  have htrace : WordTrace (prefixWord ++ tailWord_1718164) baseStart_1718164 baseEnd_1718164 := by
    simpa [prefixWord, tailWord_1718164, baseEnd_1718164] using wordTrace_append hprefix tailTrace_1718164
  have hstable : (prefixWord ++ tailWord_1718164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718164).length < 2 ^ (prefixWord ++ tailWord_1718164).sum := by decide
  have hdescent : baseEnd_1718164 < baseStart_1718164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718207 : List Nat := [1, 1, 2, 2, 2, 1, 3, 1, 4, 5]
def baseStart_1718207 : Nat := 118140960795 + 1718207 * 2 ^ 59
def prefixEnd_1718207 : Nat := 4983230072969 + 3 ^ 40 * 1718207 * 2
def baseEnd_1718207 : Nat := 588177369946576160607077

theorem tailTrace_1718207 : CollatzResearch.WordTrace tailWord_1718207 prefixEnd_1718207 588177369946576160607077 := by
  unfold tailWord_1718207
  simp only [CollatzResearch.WordTrace]
  refine ⟨62668157686236960238248875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41778771790824640158832583 62668157686236960238248875)
  ·
    refine ⟨94002236529355440357373313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62668157686236960238248875 94002236529355440357373313)
    ·
      refine ⟨70501677397016580268029985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94002236529355440357373313 70501677397016580268029985)
      ·
        refine ⟨52876258047762435201022489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70501677397016580268029985 52876258047762435201022489)
        ·
          refine ⟨39657193535821826400766867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52876258047762435201022489 39657193535821826400766867)
          ·
            refine ⟨59485790303732739601150301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39657193535821826400766867 59485790303732739601150301)
            ·
              refine ⟨22307171363899777350431363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59485790303732739601150301 22307171363899777350431363)
              ·
                refine ⟨33460757045849666025647045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22307171363899777350431363 33460757045849666025647045)
                ·
                  refine ⟨6273891946096812379808821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33460757045849666025647045 6273891946096812379808821)
                  ·
                    refine ⟨588177369946576160607077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6273891946096812379808821 588177369946576160607077)
                    ·
                      rfl

theorem cell22_1718207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 1, 4, 5].length) (baseStart_1718207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718207 prefixEnd_1718207 := by exact prefixLift 1718207
  have htrace : WordTrace (prefixWord ++ tailWord_1718207) baseStart_1718207 baseEnd_1718207 := by
    simpa [prefixWord, tailWord_1718207, baseEnd_1718207] using wordTrace_append hprefix tailTrace_1718207
  have hstable : (prefixWord ++ tailWord_1718207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718207).length < 2 ^ (prefixWord ++ tailWord_1718207).sum := by decide
  have hdescent : baseEnd_1718207 < baseStart_1718207 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718247 : List Nat := [1, 1, 5, 2, 4, 1, 1, 3, 1, 3]
def baseStart_1718247 : Nat := 118140960795 + 1718247 * 2 ^ 59
def prefixEnd_1718247 : Nat := 4983230072969 + 3 ^ 40 * 1718247 * 2
def baseEnd_1718247 : Nat := 588191062764029389606955

theorem tailTrace_1718247 : CollatzResearch.WordTrace tailWord_1718247 prefixEnd_1718247 588191062764029389606955 := by
  unfold tailWord_1718247
  simp only [CollatzResearch.WordTrace]
  refine ⟨62669616606092047069704995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41779744404061364713136663 62669616606092047069704995)
  ·
    refine ⟨94004424909138070604557493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62669616606092047069704995 94004424909138070604557493)
    ·
      refine ⟨8812914835231694119177265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 94004424909138070604557493 8812914835231694119177265)
      ·
        refine ⟨6609686126423770589382949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8812914835231694119177265 6609686126423770589382949)
        ·
          refine ⟨1239316148704456985509303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6609686126423770589382949 1239316148704456985509303)
          ·
            refine ⟨1858974223056685478263955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1239316148704456985509303 1858974223056685478263955)
            ·
              refine ⟨2788461334585028217395933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1858974223056685478263955 2788461334585028217395933)
              ·
                refine ⟨1045673000469385581523475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2788461334585028217395933 1045673000469385581523475)
                ·
                  refine ⟨1568509500704078372285213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1045673000469385581523475 1568509500704078372285213)
                  ·
                    refine ⟨588191062764029389606955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1568509500704078372285213 588191062764029389606955)
                    ·
                      rfl

theorem cell22_1718247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 3, 1, 3].length) (baseStart_1718247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718247 prefixEnd_1718247 := by exact prefixLift 1718247
  have htrace : WordTrace (prefixWord ++ tailWord_1718247) baseStart_1718247 baseEnd_1718247 := by
    simpa [prefixWord, tailWord_1718247, baseEnd_1718247] using wordTrace_append hprefix tailTrace_1718247
  have hstable : (prefixWord ++ tailWord_1718247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718247).length < 2 ^ (prefixWord ++ tailWord_1718247).sum := by decide
  have hdescent : baseEnd_1718247 < baseStart_1718247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718284 : List Nat := [2, 2, 1, 2, 3, 1, 1, 2, 4, 4]
def baseStart_1718284 : Nat := 118140960795 + 1718284 * 2 ^ 59
def prefixEnd_1718284 : Nat := 4983230072969 + 3 ^ 40 * 1718284 * 2
def baseEnd_1718284 : Nat := 588203728620173626431841

theorem tailTrace_1718284 : CollatzResearch.WordTrace tailWord_1718284 prefixEnd_1718284 588203728620173626431841 := by
  unfold tailWord_1718284
  simp only [CollatzResearch.WordTrace]
  refine ⟨31335483053479001194400953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41780644071305334925867937 31335483053479001194400953)
  ·
    refine ⟨23501612290109250895800715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31335483053479001194400953 23501612290109250895800715)
    ·
      refine ⟨35252418435163876343701073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23501612290109250895800715 35252418435163876343701073)
      ·
        refine ⟨26439313826372907257775805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35252418435163876343701073 26439313826372907257775805)
        ·
          refine ⟨9914742684889840221665927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26439313826372907257775805 9914742684889840221665927)
          ·
            refine ⟨14872114027334760332498891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9914742684889840221665927 14872114027334760332498891)
            ·
              refine ⟨22308171041002140498748337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14872114027334760332498891 22308171041002140498748337)
              ·
                refine ⟨16731128280751605374061253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22308171041002140498748337 16731128280751605374061253)
                ·
                  refine ⟨3137086552640926007636485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16731128280751605374061253 3137086552640926007636485)
                  ·
                    refine ⟨588203728620173626431841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3137086552640926007636485 588203728620173626431841)
                    ·
                      rfl

theorem cell22_1718284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 2, 4, 4].length) (baseStart_1718284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718284 prefixEnd_1718284 := by exact prefixLift 1718284
  have htrace : WordTrace (prefixWord ++ tailWord_1718284) baseStart_1718284 baseEnd_1718284 := by
    simpa [prefixWord, tailWord_1718284, baseEnd_1718284] using wordTrace_append hprefix tailTrace_1718284
  have hstable : (prefixWord ++ tailWord_1718284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718284).length < 2 ^ (prefixWord ++ tailWord_1718284).sum := by decide
  have hdescent : baseEnd_1718284 < baseStart_1718284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718301 : List Nat := [1, 4, 2, 2, 2, 1, 1, 3, 2, 4]
def baseStart_1718301 : Nat := 118140960795 + 1718301 * 2 ^ 59
def prefixEnd_1718301 : Nat := 4983230072969 + 3 ^ 40 * 1718301 * 2
def baseEnd_1718301 : Nat := 588209548067591248756789

theorem tailTrace_1718301 : CollatzResearch.WordTrace tailWord_1718301 prefixEnd_1718301 588209548067591248756789 := by
  unfold tailWord_1718301
  simp only [CollatzResearch.WordTrace]
  refine ⟨62671586147896414292170757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41781057431930942861447171 62671586147896414292170757)
  ·
    refine ⟨11750922402730577679782017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62671586147896414292170757 11750922402730577679782017)
    ·
      refine ⟨8813191802047933259836513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11750922402730577679782017 8813191802047933259836513)
      ·
        refine ⟨6609893851535949944877385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8813191802047933259836513 6609893851535949944877385)
        ·
          refine ⟨4957420388651962458658039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6609893851535949944877385 4957420388651962458658039)
          ·
            refine ⟨7436130582977943687987059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957420388651962458658039 7436130582977943687987059)
            ·
              refine ⟨11154195874466915531980589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7436130582977943687987059 11154195874466915531980589)
              ·
                refine ⟨4182823452925093324492721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11154195874466915531980589 4182823452925093324492721)
                ·
                  refine ⟨3137117589693819993369541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4182823452925093324492721 3137117589693819993369541)
                  ·
                    refine ⟨588209548067591248756789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3137117589693819993369541 588209548067591248756789)
                    ·
                      rfl

theorem cell22_1718301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 3, 2, 4].length) (baseStart_1718301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718301 prefixEnd_1718301 := by exact prefixLift 1718301
  have htrace : WordTrace (prefixWord ++ tailWord_1718301) baseStart_1718301 baseEnd_1718301 := by
    simpa [prefixWord, tailWord_1718301, baseEnd_1718301] using wordTrace_append hprefix tailTrace_1718301
  have hstable : (prefixWord ++ tailWord_1718301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718301).length < 2 ^ (prefixWord ++ tailWord_1718301).sum := by decide
  have hdescent : baseEnd_1718301 < baseStart_1718301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718408 : List Nat := [2, 1, 3, 4, 1, 1, 1, 4, 1, 4]
def baseStart_1718408 : Nat := 118140960795 + 1718408 * 2 ^ 59
def prefixEnd_1718408 : Nat := 4983230072969 + 3 ^ 40 * 1718408 * 2
def baseEnd_1718408 : Nat := 588246176354278636331461

theorem tailTrace_1718408 : CollatzResearch.WordTrace tailWord_1718408 prefixEnd_1718408 588246176354278636331461 := by
  unfold tailWord_1718408
  simp only [CollatzResearch.WordTrace]
  refine ⟨31337744379254385783157939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41783659172339181044210585 31337744379254385783157939)
  ·
    refine ⟨47006616568881578674736909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31337744379254385783157939 47006616568881578674736909)
    ·
      refine ⟨17627481213330592003026341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47006616568881578674736909 17627481213330592003026341)
      ·
        refine ⟨3305152727499486000567439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17627481213330592003026341 3305152727499486000567439)
        ·
          refine ⟨4957729091249229000851159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3305152727499486000567439 4957729091249229000851159)
          ·
            refine ⟨7436593636873843501276739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4957729091249229000851159 7436593636873843501276739)
            ·
              refine ⟨11154890455310765251915109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7436593636873843501276739 11154890455310765251915109)
              ·
                refine ⟨2091541960370768484734083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11154890455310765251915109 2091541960370768484734083)
                ·
                  refine ⟨3137312940556152727101125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2091541960370768484734083 3137312940556152727101125)
                  ·
                    refine ⟨588246176354278636331461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3137312940556152727101125 588246176354278636331461)
                    ·
                      rfl

theorem cell22_1718408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 4, 1, 4].length) (baseStart_1718408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718408 prefixEnd_1718408 := by exact prefixLift 1718408
  have htrace : WordTrace (prefixWord ++ tailWord_1718408) baseStart_1718408 baseEnd_1718408 := by
    simpa [prefixWord, tailWord_1718408, baseEnd_1718408] using wordTrace_append hprefix tailTrace_1718408
  have hstable : (prefixWord ++ tailWord_1718408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718408).length < 2 ^ (prefixWord ++ tailWord_1718408).sum := by decide
  have hdescent : baseEnd_1718408 < baseStart_1718408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718421 : List Nat := [1, 3, 2, 1, 1, 1, 3, 1, 6, 3]
def baseStart_1718421 : Nat := 118140960795 + 1718421 * 2 ^ 59
def prefixEnd_1718421 : Nat := 4983230072969 + 3 ^ 40 * 1718421 * 2
def baseEnd_1718421 : Nat := 588250626519950935756421

theorem tailTrace_1718421 : CollatzResearch.WordTrace tailWord_1718421 prefixEnd_1718421 588250626519950935756421 := by
  unfold tailWord_1718421
  simp only [CollatzResearch.WordTrace]
  refine ⟨62675962907461674786539117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41783975271641116524359411 62675962907461674786539117)
  ·
    refine ⟨23503486090298128044952169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62675962907461674786539117 23503486090298128044952169)
    ·
      refine ⟨17627614567723596033714127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23503486090298128044952169 17627614567723596033714127)
      ·
        refine ⟨26441421851585394050571191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17627614567723596033714127 26441421851585394050571191)
        ·
          refine ⟨39662132777378091075856787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26441421851585394050571191 39662132777378091075856787)
          ·
            refine ⟨59493199166067136613785181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39662132777378091075856787 59493199166067136613785181)
            ·
              refine ⟨22309949687275176230169443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59493199166067136613785181 22309949687275176230169443)
              ·
                refine ⟨33464924530912764345254165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22309949687275176230169443 33464924530912764345254165)
                ·
                  refine ⟨1568668337386535828683789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33464924530912764345254165 1568668337386535828683789)
                  ·
                    refine ⟨588250626519950935756421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1568668337386535828683789 588250626519950935756421)
                    ·
                      rfl

theorem cell22_1718421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_1718421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718421 prefixEnd_1718421 := by exact prefixLift 1718421
  have htrace : WordTrace (prefixWord ++ tailWord_1718421) baseStart_1718421 baseEnd_1718421 := by
    simpa [prefixWord, tailWord_1718421, baseEnd_1718421] using wordTrace_append hprefix tailTrace_1718421
  have hstable : (prefixWord ++ tailWord_1718421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718421).length < 2 ^ (prefixWord ++ tailWord_1718421).sum := by decide
  have hdescent : baseEnd_1718421 < baseStart_1718421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718455 : List Nat := [1, 1, 3, 1, 4, 2, 4, 1, 2, 3]
def baseStart_1718455 : Nat := 118140960795 + 1718455 * 2 ^ 59
def prefixEnd_1718455 : Nat := 4983230072969 + 3 ^ 40 * 1718455 * 2
def baseEnd_1718455 : Nat := 588262265414786180406317

theorem tailTrace_1718455 : CollatzResearch.WordTrace tailWord_1718455 prefixEnd_1718455 588262265414786180406317 := by
  unfold tailWord_1718455
  simp only [CollatzResearch.WordTrace]
  refine ⟨62677202989338498593276819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41784801992892332395517879 62677202989338498593276819)
  ·
    refine ⟨94015804484007747889915229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62677202989338498593276819 94015804484007747889915229)
    ·
      refine ⟨35255926681502905458718211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94015804484007747889915229 35255926681502905458718211)
      ·
        refine ⟨52883890022254358188077317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35255926681502905458718211 52883890022254358188077317)
        ·
          refine ⟨9915729379172692160264497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52883890022254358188077317 9915729379172692160264497)
          ·
            refine ⟨7436797034379519120198373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9915729379172692160264497 7436797034379519120198373)
            ·
              refine ⟨1394399443946159835037195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7436797034379519120198373 1394399443946159835037195)
              ·
                refine ⟨2091599165919239752555793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1394399443946159835037195 2091599165919239752555793)
                ·
                  refine ⟨1568699374439429814416845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2091599165919239752555793 1568699374439429814416845)
                  ·
                    refine ⟨588262265414786180406317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1568699374439429814416845 588262265414786180406317)
                    ·
                      rfl

theorem cell22_1718455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 1, 2, 3].length) (baseStart_1718455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718455 prefixEnd_1718455 := by exact prefixLift 1718455
  have htrace : WordTrace (prefixWord ++ tailWord_1718455) baseStart_1718455 baseEnd_1718455 := by
    simpa [prefixWord, tailWord_1718455, baseEnd_1718455] using wordTrace_append hprefix tailTrace_1718455
  have hstable : (prefixWord ++ tailWord_1718455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718455).length < 2 ^ (prefixWord ++ tailWord_1718455).sum := by decide
  have hdescent : baseEnd_1718455 < baseStart_1718455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718511 : List Nat := [1, 1, 2, 1, 6, 1, 1, 1, 1, 7]
def baseStart_1718511 : Nat := 118140960795 + 1718511 * 2 ^ 59
def prefixEnd_1718511 : Nat := 4983230072969 + 3 ^ 40 * 1718511 * 2
def baseEnd_1718511 : Nat := 588281435359220701006145

theorem tailTrace_1718511 : CollatzResearch.WordTrace tailWord_1718511 prefixEnd_1718511 588281435359220701006145 := by
  unfold tailWord_1718511
  simp only [CollatzResearch.WordTrace]
  refine ⟨62679245477135620157315387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41786163651423746771543591 62679245477135620157315387)
  ·
    refine ⟨94018868215703430235973081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62679245477135620157315387 94018868215703430235973081)
    ·
      refine ⟨70514151161777572676979811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94018868215703430235973081 70514151161777572676979811)
      ·
        refine ⟨105771226742666359015469717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70514151161777572676979811 105771226742666359015469717)
        ·
          refine ⟨4958026253562485578850143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105771226742666359015469717 4958026253562485578850143)
          ·
            refine ⟨7437039380343728368275215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4958026253562485578850143 7437039380343728368275215)
            ·
              refine ⟨11155559070515592552412823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7437039380343728368275215 11155559070515592552412823)
              ·
                refine ⟨16733338605773388828619235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11155559070515592552412823 16733338605773388828619235)
                ·
                  refine ⟨25100007908660083242928853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16733338605773388828619235 25100007908660083242928853)
                  ·
                    refine ⟨588281435359220701006145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25100007908660083242928853 588281435359220701006145)
                    ·
                      rfl

theorem cell22_1718511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 1, 1, 1, 7].length) (baseStart_1718511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718511 prefixEnd_1718511 := by exact prefixLift 1718511
  have htrace : WordTrace (prefixWord ++ tailWord_1718511) baseStart_1718511 baseEnd_1718511 := by
    simpa [prefixWord, tailWord_1718511, baseEnd_1718511] using wordTrace_append hprefix tailTrace_1718511
  have hstable : (prefixWord ++ tailWord_1718511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718511).length < 2 ^ (prefixWord ++ tailWord_1718511).sum := by decide
  have hdescent : baseEnd_1718511 < baseStart_1718511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718588 : List Nat := [2, 2, 2, 2, 1, 2, 2, 3, 2, 4]
def baseStart_1718588 : Nat := 118140960795 + 1718588 * 2 ^ 59
def prefixEnd_1718588 : Nat := 4983230072969 + 3 ^ 40 * 1718588 * 2
def baseEnd_1718588 : Nat := 588307794032818166830909

theorem tailTrace_1718588 : CollatzResearch.WordTrace tailWord_1718588 prefixEnd_1718588 588307794032818166830909 := by
  unfold tailWord_1718588
  simp only [CollatzResearch.WordTrace]
  refine ⟨31341026948928331153934209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41788035931904441538578945 31341026948928331153934209)
  ·
    refine ⟨23505770211696248365450657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31341026948928331153934209 23505770211696248365450657)
    ·
      refine ⟨17629327658772186274087993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23505770211696248365450657 17629327658772186274087993)
      ·
        refine ⟨13221995744079139705565995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17629327658772186274087993 13221995744079139705565995)
        ·
          refine ⟨19832993616118709558348993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13221995744079139705565995 19832993616118709558348993)
          ·
            refine ⟨14874745212089032168761745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19832993616118709558348993 14874745212089032168761745)
            ·
              refine ⟨11156058909066774126571309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14874745212089032168761745 11156058909066774126571309)
              ·
                refine ⟨4183522090900040297464241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11156058909066774126571309 4183522090900040297464241)
                ·
                  refine ⟨3137641568175030223098181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4183522090900040297464241 3137641568175030223098181)
                  ·
                    refine ⟨588307794032818166830909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3137641568175030223098181 588307794032818166830909)
                    ·
                      rfl

theorem cell22_1718588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_1718588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718588 prefixEnd_1718588 := by exact prefixLift 1718588
  have htrace : WordTrace (prefixWord ++ tailWord_1718588) baseStart_1718588 baseEnd_1718588 := by
    simpa [prefixWord, tailWord_1718588, baseEnd_1718588] using wordTrace_append hprefix tailTrace_1718588
  have hstable : (prefixWord ++ tailWord_1718588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718588).length < 2 ^ (prefixWord ++ tailWord_1718588).sum := by decide
  have hdescent : baseEnd_1718588 < baseStart_1718588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718590 : List Nat := [4, 2, 1, 2, 1, 2, 1, 2, 4, 3]
def baseStart_1718590 : Nat := 118140960795 + 1718590 * 2 ^ 59
def prefixEnd_1718590 : Nat := 4983230072969 + 3 ^ 40 * 1718590 * 2
def baseEnd_1718590 : Nat := 588308478673690828280903

theorem tailTrace_1718590 : CollatzResearch.WordTrace tailWord_1718590 prefixEnd_1718590 588308478673690828280903 := by
  unfold tailWord_1718590
  simp only [CollatzResearch.WordTrace]
  refine ⟨7835265855481177081180153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41788084562566277766294149 7835265855481177081180153)
  ·
    refine ⟨5876449391610882810885115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7835265855481177081180153 5876449391610882810885115)
    ·
      refine ⟨8814674087416324216327673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5876449391610882810885115 8814674087416324216327673)
      ·
        refine ⟨6611005565562243162245755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8814674087416324216327673 6611005565562243162245755)
        ·
          refine ⟨9916508348343364743368633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6611005565562243162245755 9916508348343364743368633)
          ·
            refine ⟨7437381261257523557526475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9916508348343364743368633 7437381261257523557526475)
            ·
              refine ⟨11156071891886285336289713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7437381261257523557526475 11156071891886285336289713)
              ·
                refine ⟨8367053918914714002217285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11156071891886285336289713 8367053918914714002217285)
                ·
                  refine ⟨1568822609796508875415741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8367053918914714002217285 1568822609796508875415741)
                  ·
                    refine ⟨588308478673690828280903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1568822609796508875415741 588308478673690828280903)
                    ·
                      rfl

theorem cell22_1718590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 2, 4, 3].length) (baseStart_1718590 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718590 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718590 prefixEnd_1718590 := by exact prefixLift 1718590
  have htrace : WordTrace (prefixWord ++ tailWord_1718590) baseStart_1718590 baseEnd_1718590 := by
    simpa [prefixWord, tailWord_1718590, baseEnd_1718590] using wordTrace_append hprefix tailTrace_1718590
  have hstable : (prefixWord ++ tailWord_1718590).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718590).length < 2 ^ (prefixWord ++ tailWord_1718590).sum := by decide
  have hdescent : baseEnd_1718590 < baseStart_1718590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718624 : List Nat := [2, 1, 1, 3, 5, 2, 2, 1, 2, 3]
def baseStart_1718624 : Nat := 118140960795 + 1718624 * 2 ^ 59
def prefixEnd_1718624 : Nat := 4983230072969 + 3 ^ 40 * 1718624 * 2
def baseEnd_1718624 : Nat := 588320117568526072930799

theorem tailTrace_1718624 : CollatzResearch.WordTrace tailWord_1718624 prefixEnd_1718624 588320117568526072930799 := by
  unfold tailWord_1718624
  simp only [CollatzResearch.WordTrace]
  refine ⟨31341683462863120228089463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41788911283817493637452617 31341683462863120228089463)
  ·
    refine ⟨47012525194294680342134195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31341683462863120228089463 47012525194294680342134195)
    ·
      refine ⟨70518787791442020513201293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47012525194294680342134195 70518787791442020513201293)
      ·
        refine ⟨26444545421790757692450485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70518787791442020513201293 26444545421790757692450485)
        ·
          refine ⟨2479176133292883533667233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 26444545421790757692450485 2479176133292883533667233)
          ·
            refine ⟨1859382099969662650250425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2479176133292883533667233 1859382099969662650250425)
            ·
              refine ⟨1394536574977246987687819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1859382099969662650250425 1394536574977246987687819)
              ·
                refine ⟨2091804862465870481531729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1394536574977246987687819 2091804862465870481531729)
                ·
                  refine ⟨1568853646849402861148797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2091804862465870481531729 1568853646849402861148797)
                  ·
                    refine ⟨588320117568526072930799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1568853646849402861148797 588320117568526072930799)
                    ·
                      rfl

theorem cell22_1718624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 1, 2, 3].length) (baseStart_1718624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718624 prefixEnd_1718624 := by exact prefixLift 1718624
  have htrace : WordTrace (prefixWord ++ tailWord_1718624) baseStart_1718624 baseEnd_1718624 := by
    simpa [prefixWord, tailWord_1718624, baseEnd_1718624] using wordTrace_append hprefix tailTrace_1718624
  have hstable : (prefixWord ++ tailWord_1718624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718624).length < 2 ^ (prefixWord ++ tailWord_1718624).sum := by decide
  have hdescent : baseEnd_1718624 < baseStart_1718624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718663 : List Nat := [1, 1, 4, 2, 2, 1, 2, 2, 2, 5]
def baseStart_1718663 : Nat := 118140960795 + 1718663 * 2 ^ 59
def prefixEnd_1718663 : Nat := 4983230072969 + 3 ^ 40 * 1718663 * 2
def baseEnd_1718663 : Nat := 588333468065542971205679

theorem tailTrace_1718663 : CollatzResearch.WordTrace tailWord_1718663 prefixEnd_1718663 588333468065542971205679 := by
  unfold tailWord_1718663
  simp only [CollatzResearch.WordTrace]
  refine ⟨62684789372584950116848643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41789859581723300077899095 62684789372584950116848643)
  ·
    refine ⟨94027184058877425175272965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62684789372584950116848643 94027184058877425175272965)
    ·
      refine ⟨17630097011039517220363681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 94027184058877425175272965 17630097011039517220363681)
      ·
        refine ⟨13222572758279637915272761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17630097011039517220363681 13222572758279637915272761)
        ·
          refine ⟨9916929568709728436454571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13222572758279637915272761 9916929568709728436454571)
          ·
            refine ⟨14875394353064592654681857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9916929568709728436454571 14875394353064592654681857)
            ·
              refine ⟨11156545764798444491011393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14875394353064592654681857 11156545764798444491011393)
              ·
                refine ⟨8367409323598833368258545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11156545764798444491011393 8367409323598833368258545)
                ·
                  refine ⟨6275556992699125026193909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8367409323598833368258545 6275556992699125026193909)
                  ·
                    refine ⟨588333468065542971205679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6275556992699125026193909 588333468065542971205679)
                    ·
                      rfl

theorem cell22_1718663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_1718663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718663 prefixEnd_1718663 := by exact prefixLift 1718663
  have htrace : WordTrace (prefixWord ++ tailWord_1718663) baseStart_1718663 baseEnd_1718663 := by
    simpa [prefixWord, tailWord_1718663, baseEnd_1718663] using wordTrace_append hprefix tailTrace_1718663
  have hstable : (prefixWord ++ tailWord_1718663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718663).length < 2 ^ (prefixWord ++ tailWord_1718663).sum := by decide
  have hdescent : baseEnd_1718663 < baseStart_1718663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718665 : List Nat := [1, 2, 1, 1, 6, 2, 2, 2, 5]
def baseStart_1718665 : Nat := 118140960795 + 1718665 * 2 ^ 59
def prefixEnd_1718665 : Nat := 4983230072969 + 3 ^ 40 * 1718665 * 2
def baseEnd_1718665 : Nat := 196111384235471877551891

theorem tailTrace_1718665 : CollatzResearch.WordTrace tailWord_1718665 prefixEnd_1718665 196111384235471877551891 := by
  unfold tailWord_1718665
  simp only [CollatzResearch.WordTrace]
  refine ⟨62684862318577704458421449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41789908212385136305614299 62684862318577704458421449)
  ·
    refine ⟨47013646738933278343816087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62684862318577704458421449 47013646738933278343816087)
    ·
      refine ⟨70520470108399917515724131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47013646738933278343816087 70520470108399917515724131)
      ·
        refine ⟨105780705162599876273586197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70520470108399917515724131 105780705162599876273586197)
        ·
          refine ⟨4958470554496869200324353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105780705162599876273586197 4958470554496869200324353)
          ·
            refine ⟨3718852915872651900243265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4958470554496869200324353 3718852915872651900243265)
            ·
              refine ⟨2789139686904488925182449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3718852915872651900243265 2789139686904488925182449)
              ·
                refine ⟨2091854765178366693886837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2789139686904488925182449 2091854765178366693886837)
                ·
                  refine ⟨196111384235471877551891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2091854765178366693886837 196111384235471877551891)
                  ·
                    rfl

theorem cell22_1718665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 2, 2, 2, 5].length) (baseStart_1718665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718665 prefixEnd_1718665 := by exact prefixLift 1718665
  have htrace : WordTrace (prefixWord ++ tailWord_1718665) baseStart_1718665 baseEnd_1718665 := by
    simpa [prefixWord, tailWord_1718665, baseEnd_1718665] using wordTrace_append hprefix tailTrace_1718665
  have hstable : (prefixWord ++ tailWord_1718665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718665).length < 2 ^ (prefixWord ++ tailWord_1718665).sum := by decide
  have hdescent : baseEnd_1718665 < baseStart_1718665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718680 : List Nat := [2, 1, 2, 5, 1, 2, 1, 1, 2, 5]
def baseStart_1718680 : Nat := 118140960795 + 1718680 * 2 ^ 59
def prefixEnd_1718680 : Nat := 4983230072969 + 3 ^ 40 * 1718680 * 2
def baseEnd_1718680 : Nat := 588339287512960593530627

theorem tailTrace_1718680 : CollatzResearch.WordTrace tailWord_1718680 prefixEnd_1718680 588339287512960593530627 := by
  unfold tailWord_1718680
  simp only [CollatzResearch.WordTrace]
  refine ⟨31342704706761681010108747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41790272942348908013478329 31342704706761681010108747)
  ·
    refine ⟨47014057060142521515163121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31342704706761681010108747 47014057060142521515163121)
    ·
      refine ⟨35260542795106891136372341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47014057060142521515163121 35260542795106891136372341)
      ·
        refine ⟨3305675887041271044034907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 35260542795106891136372341 3305675887041271044034907)
        ·
          refine ⟨4958513830561906566052361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3305675887041271044034907 4958513830561906566052361)
          ·
            refine ⟨3718885372921429924539271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4958513830561906566052361 3718885372921429924539271)
            ·
              refine ⟨5578328059382144886808907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3718885372921429924539271 5578328059382144886808907)
              ·
                refine ⟨8367492089073217330213361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578328059382144886808907 8367492089073217330213361)
                ·
                  refine ⟨6275619066804912997660021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8367492089073217330213361 6275619066804912997660021)
                  ·
                    refine ⟨588339287512960593530627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6275619066804912997660021 588339287512960593530627)
                    ·
                      rfl

theorem cell22_1718680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_1718680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718680 prefixEnd_1718680 := by exact prefixLift 1718680
  have htrace : WordTrace (prefixWord ++ tailWord_1718680) baseStart_1718680 baseEnd_1718680 := by
    simpa [prefixWord, tailWord_1718680, baseEnd_1718680] using wordTrace_append hprefix tailTrace_1718680
  have hstable : (prefixWord ++ tailWord_1718680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718680).length < 2 ^ (prefixWord ++ tailWord_1718680).sum := by decide
  have hdescent : baseEnd_1718680 < baseStart_1718680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718693 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 6]
def baseStart_1718693 : Nat := 118140960795 + 1718693 * 2 ^ 59
def prefixEnd_1718693 : Nat := 4983230072969 + 3 ^ 40 * 1718693 * 2
def baseEnd_1718693 : Nat := 196114579226210964318529

theorem tailTrace_1718693 : CollatzResearch.WordTrace tailWord_1718693 prefixEnd_1718693 196114579226210964318529 := by
  unfold tailWord_1718693
  simp only [CollatzResearch.WordTrace]
  refine ⟨62685883562476265240440733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41790589041650843493627155 62685883562476265240440733)
  ·
    refine ⟨23507206335928599465165275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62685883562476265240440733 23507206335928599465165275)
    ·
      refine ⟨35260809503892899197747913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23507206335928599465165275 35260809503892899197747913)
      ·
        refine ⟨26445607127919674398310935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35260809503892899197747913 26445607127919674398310935)
        ·
          refine ⟨39668410691879511597466403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26445607127919674398310935 39668410691879511597466403)
          ·
            refine ⟨59502616037819267396199605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39668410691879511597466403 59502616037819267396199605)
            ·
              refine ⟨5578370253545556318393713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59502616037819267396199605 5578370253545556318393713)
              ·
                refine ⟨4183777690159167238795285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5578370253545556318393713 4183777690159167238795285)
                ·
                  refine ⟨196114579226210964318529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4183777690159167238795285 196114579226210964318529)
                  ·
                    rfl

theorem cell22_1718693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 6].length) (baseStart_1718693 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718693 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718693 prefixEnd_1718693 := by exact prefixLift 1718693
  have htrace : WordTrace (prefixWord ++ tailWord_1718693) baseStart_1718693 baseEnd_1718693 := by
    simpa [prefixWord, tailWord_1718693, baseEnd_1718693] using wordTrace_append hprefix tailTrace_1718693
  have hstable : (prefixWord ++ tailWord_1718693).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718693).length < 2 ^ (prefixWord ++ tailWord_1718693).sum := by decide
  have hdescent : baseEnd_1718693 < baseStart_1718693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718695 : List Nat := [1, 1, 6, 1, 1, 2, 2, 1, 3, 4]
def baseStart_1718695 : Nat := 118140960795 + 1718695 * 2 ^ 59
def prefixEnd_1718695 : Nat := 4983230072969 + 3 ^ 40 * 1718695 * 2
def baseEnd_1718695 : Nat := 588344422319505554405581

theorem tailTrace_1718695 : CollatzResearch.WordTrace tailWord_1718695 prefixEnd_1718695 588344422319505554405581 := by
  unfold tailWord_1718695
  simp only [CollatzResearch.WordTrace]
  refine ⟨62685956508469019582013539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41790637672312679721342359 62685956508469019582013539)
  ·
    refine ⟨94028934762703529373020309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62685956508469019582013539 94028934762703529373020309)
    ·
      refine ⟨4407606317001727939360327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 94028934762703529373020309 4407606317001727939360327)
      ·
        refine ⟨6611409475502591909040491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4407606317001727939360327 6611409475502591909040491)
        ·
          refine ⟨9917114213253887863560737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6611409475502591909040491 9917114213253887863560737)
          ·
            refine ⟨7437835659940415897670553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9917114213253887863560737 7437835659940415897670553)
            ·
              refine ⟨5578376744955311923252915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7437835659940415897670553 5578376744955311923252915)
              ·
                refine ⟨8367565117432967884879373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5578376744955311923252915 8367565117432967884879373)
                ·
                  refine ⟨3137836919037362956829765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8367565117432967884879373 3137836919037362956829765)
                  ·
                    refine ⟨588344422319505554405581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3137836919037362956829765 588344422319505554405581)
                    ·
                      rfl

theorem cell22_1718695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_1718695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718695 prefixEnd_1718695 := by exact prefixLift 1718695
  have htrace : WordTrace (prefixWord ++ tailWord_1718695) baseStart_1718695 baseEnd_1718695 := by
    simpa [prefixWord, tailWord_1718695, baseEnd_1718695] using wordTrace_append hprefix tailTrace_1718695
  have hstable : (prefixWord ++ tailWord_1718695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718695).length < 2 ^ (prefixWord ++ tailWord_1718695).sum := by decide
  have hdescent : baseEnd_1718695 < baseStart_1718695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718723 : List Nat := [1, 1, 1, 3, 1, 1, 3, 3, 4, 4]
def baseStart_1718723 : Nat := 118140960795 + 1718723 * 2 ^ 59
def prefixEnd_1718723 : Nat := 4983230072969 + 3 ^ 40 * 1718723 * 2
def baseEnd_1718723 : Nat := 588354007291722814705495

theorem tailTrace_1718723 : CollatzResearch.WordTrace tailWord_1718723 prefixEnd_1718723 588354007291722814705495 := by
  unfold tailWord_1718723
  simp only [CollatzResearch.WordTrace]
  refine ⟨62686977752367580364032823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41791318501578386909355215 62686977752367580364032823)
  ·
    refine ⟨94030466628551370546049235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62686977752367580364032823 94030466628551370546049235)
    ·
      refine ⟨141045699942827055819073853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94030466628551370546049235 141045699942827055819073853)
      ·
        refine ⟨52892137478560145932152695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 141045699942827055819073853 52892137478560145932152695)
        ·
          refine ⟨79338206217840218898229043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52892137478560145932152695 79338206217840218898229043)
          ·
            refine ⟨119007309326760328347343565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 79338206217840218898229043 119007309326760328347343565)
            ·
              refine ⟨44627740997535123130253837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 119007309326760328347343565 44627740997535123130253837)
              ·
                refine ⟨16735402874075671173845189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44627740997535123130253837 16735402874075671173845189)
                ·
                  refine ⟨3137888038889188345095973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16735402874075671173845189 3137888038889188345095973)
                  ·
                    refine ⟨588354007291722814705495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3137888038889188345095973 588354007291722814705495)
                    ·
                      rfl

theorem cell22_1718723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 3, 4, 4].length) (baseStart_1718723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718723 prefixEnd_1718723 := by exact prefixLift 1718723
  have htrace : WordTrace (prefixWord ++ tailWord_1718723) baseStart_1718723 baseEnd_1718723 := by
    simpa [prefixWord, tailWord_1718723, baseEnd_1718723] using wordTrace_append hprefix tailTrace_1718723
  have hstable : (prefixWord ++ tailWord_1718723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718723).length < 2 ^ (prefixWord ++ tailWord_1718723).sum := by decide
  have hdescent : baseEnd_1718723 < baseStart_1718723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718740 : List Nat := [2, 4, 1, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1718740 : Nat := 118140960795 + 1718740 * 2 ^ 59
def prefixEnd_1718740 : Nat := 4983230072969 + 3 ^ 40 * 1718740 * 2
def baseEnd_1718740 : Nat := 588359826739140437030443

theorem tailTrace_1718740 : CollatzResearch.WordTrace tailWord_1718740 prefixEnd_1718740 588359826739140437030443 := by
  unfold tailWord_1718740
  simp only [CollatzResearch.WordTrace]
  refine ⟨31343798896652996133700837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41791731862203994844934449 31343798896652996133700837)
  ·
    refine ⟨5876962293122436775068907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31343798896652996133700837 5876962293122436775068907)
    ·
      refine ⟨8815443439683655162603361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5876962293122436775068907 8815443439683655162603361)
      ·
        refine ⟨6611582579762741371952521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8815443439683655162603361 6611582579762741371952521)
        ·
          refine ⟨4958686934822056028964391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6611582579762741371952521 4958686934822056028964391)
          ·
            refine ⟨7438030402233084043446587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4958686934822056028964391 7438030402233084043446587)
            ·
              refine ⟨11157045603349626065169881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7438030402233084043446587 11157045603349626065169881)
              ·
                refine ⟨8367784202512219548877411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11157045603349626065169881 8367784202512219548877411)
                ·
                  refine ⟨12551676303768329323316117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8367784202512219548877411 12551676303768329323316117)
                  ·
                    refine ⟨588359826739140437030443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12551676303768329323316117 588359826739140437030443)
                    ·
                      rfl

theorem cell22_1718740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1718740 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718740 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718740 prefixEnd_1718740 := by exact prefixLift 1718740
  have htrace : WordTrace (prefixWord ++ tailWord_1718740) baseStart_1718740 baseEnd_1718740 := by
    simpa [prefixWord, tailWord_1718740, baseEnd_1718740] using wordTrace_append hprefix tailTrace_1718740
  have hstable : (prefixWord ++ tailWord_1718740).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718740).length < 2 ^ (prefixWord ++ tailWord_1718740).sum := by decide
  have hdescent : baseEnd_1718740 < baseStart_1718740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718753 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 2, 7]
def baseStart_1718753 : Nat := 118140960795 + 1718753 * 2 ^ 59
def prefixEnd_1718753 : Nat := 4983230072969 + 3 ^ 40 * 1718753 * 2
def baseEnd_1718753 : Nat := 588364276904812736455403

theorem tailTrace_1718753 : CollatzResearch.WordTrace tailWord_1718753 prefixEnd_1718753 588364276904812736455403 := by
  unfold tailWord_1718753
  simp only [CollatzResearch.WordTrace]
  refine ⟨62688071942258895487624913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41792047961505930325083275 62688071942258895487624913)
  ·
    refine ⟨47016053956694171615718685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62688071942258895487624913 47016053956694171615718685)
    ·
      refine ⟨17631020233760314355894507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47016053956694171615718685 17631020233760314355894507)
      ·
        refine ⟨26446530350640471533841761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17631020233760314355894507 26446530350640471533841761)
        ·
          refine ⟨19834897762980353650381321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26446530350640471533841761 19834897762980353650381321)
          ·
            refine ⟨14876173322235265237785991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19834897762980353650381321 14876173322235265237785991)
            ·
              refine ⟨22314259983352897856678987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14876173322235265237785991 22314259983352897856678987)
              ·
                refine ⟨33471389975029346785018481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22314259983352897856678987 33471389975029346785018481)
                ·
                  refine ⟨25103542481272010088763861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33471389975029346785018481 25103542481272010088763861)
                  ·
                    refine ⟨588364276904812736455403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25103542481272010088763861 588364276904812736455403)
                    ·
                      rfl

theorem cell22_1718753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 2, 7].length) (baseStart_1718753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718753 prefixEnd_1718753 := by exact prefixLift 1718753
  have htrace : WordTrace (prefixWord ++ tailWord_1718753) baseStart_1718753 baseEnd_1718753 := by
    simpa [prefixWord, tailWord_1718753, baseEnd_1718753] using wordTrace_append hprefix tailTrace_1718753
  have hstable : (prefixWord ++ tailWord_1718753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718753).length < 2 ^ (prefixWord ++ tailWord_1718753).sum := by decide
  have hdescent : baseEnd_1718753 < baseStart_1718753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718755 : List Nat := [1, 1, 1, 6, 3, 1, 1, 8]
def baseStart_1718755 : Nat := 118140960795 + 1718755 * 2 ^ 59
def prefixEnd_1718755 : Nat := 4983230072969 + 3 ^ 40 * 1718755 * 2
def baseEnd_1718755 : Nat := 65373884616187266433933

theorem tailTrace_1718755 : CollatzResearch.WordTrace tailWord_1718755 prefixEnd_1718755 65373884616187266433933 := by
  unfold tailWord_1718755
  simp only [CollatzResearch.WordTrace]
  refine ⟨62688144888251649829197719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41792096592167766552798479 62688144888251649829197719)
  ·
    refine ⟨94032217332377474743796579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62688144888251649829197719 94032217332377474743796579)
    ·
      refine ⟨141048325998566212115694869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94032217332377474743796579 141048325998566212115694869)
      ·
        refine ⟨6611640281182791192923197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 141048325998566212115694869 6611640281182791192923197)
        ·
          refine ⟨2479365105443546697346199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6611640281182791192923197 2479365105443546697346199)
          ·
            refine ⟨3719047658165320046019299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2479365105443546697346199 3719047658165320046019299)
            ·
              refine ⟨5578571487247980069028949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719047658165320046019299 5578571487247980069028949)
              ·
                refine ⟨65373884616187266433933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5578571487247980069028949 65373884616187266433933)
                ·
                  rfl

theorem cell22_1718755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 8].length) (baseStart_1718755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718755 prefixEnd_1718755 := by exact prefixLift 1718755
  have htrace : WordTrace (prefixWord ++ tailWord_1718755) baseStart_1718755 baseEnd_1718755 := by
    simpa [prefixWord, tailWord_1718755, baseEnd_1718755] using wordTrace_append hprefix tailTrace_1718755
  have hstable : (prefixWord ++ tailWord_1718755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718755).length < 2 ^ (prefixWord ++ tailWord_1718755).sum := by decide
  have hdescent : baseEnd_1718755 < baseStart_1718755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718783 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 7]
def baseStart_1718783 : Nat := 118140960795 + 1718783 * 2 ^ 59
def prefixEnd_1718783 : Nat := 4983230072969 + 3 ^ 40 * 1718783 * 2
def baseEnd_1718783 : Nat := 196124848839300886068437

theorem tailTrace_1718783 : CollatzResearch.WordTrace tailWord_1718783 prefixEnd_1718783 196124848839300886068437 := by
  unfold tailWord_1718783
  simp only [CollatzResearch.WordTrace]
  refine ⟨62689166132150210611217003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41792777421433473740811335 62689166132150210611217003)
  ·
    refine ⟨94033749198225315916825505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62689166132150210611217003 94033749198225315916825505)
    ·
      refine ⟨70525311898668986937619129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 94033749198225315916825505 70525311898668986937619129)
      ·
        refine ⟨52893983924001740203214347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70525311898668986937619129 52893983924001740203214347)
        ·
          refine ⟨79340975886002610304821521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52893983924001740203214347 79340975886002610304821521)
          ·
            refine ⟨59505731914501957728616141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 79340975886002610304821521 59505731914501957728616141)
            ·
              refine ⟨22314649467938234148231053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59505731914501957728616141 22314649467938234148231053)
              ·
                refine ⟨8367993550476837805586645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22314649467938234148231053 8367993550476837805586645)
                ·
                  refine ⟨196124848839300886068437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8367993550476837805586645 196124848839300886068437)
                  ·
                    rfl

theorem cell22_1718783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 7].length) (baseStart_1718783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718783 prefixEnd_1718783 := by exact prefixLift 1718783
  have htrace : WordTrace (prefixWord ++ tailWord_1718783) baseStart_1718783 baseEnd_1718783 := by
    simpa [prefixWord, tailWord_1718783, baseEnd_1718783] using wordTrace_append hprefix tailTrace_1718783
  have hstable : (prefixWord ++ tailWord_1718783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718783).length < 2 ^ (prefixWord ++ tailWord_1718783).sum := by decide
  have hdescent : baseEnd_1718783 < baseStart_1718783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718838 : List Nat := [5, 1, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_1718838 : Nat := 118140960795 + 1718838 * 2 ^ 59
def prefixEnd_1718838 : Nat := 4983230072969 + 3 ^ 40 * 1718838 * 2
def baseEnd_1718838 : Nat := 588393374141900848080143

theorem tailTrace_1718838 : CollatzResearch.WordTrace tailWord_1718838 prefixEnd_1718838 588393374141900848080143 := by
  unfold tailWord_1718838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3918198259184434687779323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41794114764633970002979445 3918198259184434687779323)
  ·
    refine ⟨5877297388776652031668985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3918198259184434687779323 5877297388776652031668985)
    ·
      refine ⟨4407973041582489023751739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5877297388776652031668985 4407973041582489023751739)
      ·
        refine ⟨6611959562373733535627609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4407973041582489023751739 6611959562373733535627609)
        ·
          refine ⟨4958969671780300151720707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6611959562373733535627609 4958969671780300151720707)
          ·
            refine ⟨7438454507670450227581061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4958969671780300151720707 7438454507670450227581061)
            ·
              refine ⟨1394710220188209417671449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7438454507670450227581061 1394710220188209417671449)
              ·
                refine ⟨1046032665141157063253587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1394710220188209417671449 1046032665141157063253587)
                ·
                  refine ⟨1569048997711735594880381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046032665141157063253587 1569048997711735594880381)
                  ·
                    refine ⟨588393374141900848080143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1569048997711735594880381 588393374141900848080143)
                    ·
                      rfl

theorem cell22_1718838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_1718838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718838 prefixEnd_1718838 := by exact prefixLift 1718838
  have htrace : WordTrace (prefixWord ++ tailWord_1718838) baseStart_1718838 baseEnd_1718838 := by
    simpa [prefixWord, tailWord_1718838, baseEnd_1718838] using wordTrace_append hprefix tailTrace_1718838
  have hstable : (prefixWord ++ tailWord_1718838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718838).length < 2 ^ (prefixWord ++ tailWord_1718838).sum := by decide
  have hdescent : baseEnd_1718838 < baseStart_1718838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718890 : List Nat := [3, 1, 3, 2, 1, 1, 11]
def baseStart_1718890 : Nat := 118140960795 + 1718890 * 2 ^ 59
def prefixEnd_1718890 : Nat := 4983230072969 + 3 ^ 40 * 1718890 * 2
def baseEnd_1718890 : Nat := 21793006474244075769629

theorem tailTrace_1718890 : CollatzResearch.WordTrace tailWord_1718890 prefixEnd_1718890 21793006474244075769629 := by
  unfold tailWord_1718890
  simp only [CollatzResearch.WordTrace]
  refine ⟨15673267185690641971340531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41795379161841711923574749 15673267185690641971340531)
  ·
    refine ⟨23509900778535962957010797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15673267185690641971340531 23509900778535962957010797)
    ·
      refine ⟨8816212791950986108879049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23509900778535962957010797 8816212791950986108879049)
      ·
        refine ⟨6612159593963239581659287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8816212791950986108879049 6612159593963239581659287)
        ·
          refine ⟨9918239390944859372488931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6612159593963239581659287 9918239390944859372488931)
          ·
            refine ⟨14877359086417289058733397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9918239390944859372488931 14877359086417289058733397)
            ·
              refine ⟨21793006474244075769629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 14877359086417289058733397 21793006474244075769629)
              ·
                rfl

theorem cell22_1718890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 11].length) (baseStart_1718890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718890 prefixEnd_1718890 := by exact prefixLift 1718890
  have htrace : WordTrace (prefixWord ++ tailWord_1718890) baseStart_1718890 baseEnd_1718890 := by
    simpa [prefixWord, tailWord_1718890, baseEnd_1718890] using wordTrace_append hprefix tailTrace_1718890
  have hstable : (prefixWord ++ tailWord_1718890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718890).length < 2 ^ (prefixWord ++ tailWord_1718890).sum := by decide
  have hdescent : baseEnd_1718890 < baseStart_1718890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718894 : List Nat := [4, 1, 2, 2, 2, 2, 1, 1, 4, 3]
def baseStart_1718894 : Nat := 118140960795 + 1718894 * 2 ^ 59
def prefixEnd_1718894 : Nat := 4983230072969 + 3 ^ 40 * 1718894 * 2
def baseEnd_1718894 : Nat := 588412544086335368679971

theorem tailTrace_1718894 : CollatzResearch.WordTrace tailWord_1718894 prefixEnd_1718894 588412544086335368679971 := by
  unfold tailWord_1718894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7836651829343509571063467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41795476423165384379005157 7836651829343509571063467)
  ·
    refine ⟨11754977744015264356595201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7836651829343509571063467 11754977744015264356595201)
    ·
      refine ⟨8816233308011448267446401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11754977744015264356595201 8816233308011448267446401)
      ·
        refine ⟨6612174981008586200584801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8816233308011448267446401 6612174981008586200584801)
        ·
          refine ⟨4959131235756439650438601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6612174981008586200584801 4959131235756439650438601)
          ·
            refine ⟨3719348426817329737828951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4959131235756439650438601 3719348426817329737828951)
            ·
              refine ⟨5579022640225994606743427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3719348426817329737828951 5579022640225994606743427)
              ·
                refine ⟨8368533960338991910115141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5579022640225994606743427 8368533960338991910115141)
                ·
                  refine ⟨1569100117563560983146589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8368533960338991910115141 1569100117563560983146589)
                  ·
                    refine ⟨588412544086335368679971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1569100117563560983146589 588412544086335368679971)
                    ·
                      rfl

theorem cell22_1718894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_1718894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718894 prefixEnd_1718894 := by exact prefixLift 1718894
  have htrace : WordTrace (prefixWord ++ tailWord_1718894) baseStart_1718894 baseEnd_1718894 := by
    simpa [prefixWord, tailWord_1718894, baseEnd_1718894] using wordTrace_append hprefix tailTrace_1718894
  have hstable : (prefixWord ++ tailWord_1718894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718894).length < 2 ^ (prefixWord ++ tailWord_1718894).sum := by decide
  have hdescent : baseEnd_1718894 < baseStart_1718894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1718935 : List Nat := [1, 1, 3, 3, 2, 1, 1, 1, 9]
def baseStart_1718935 : Nat := 118140960795 + 1718935 * 2 ^ 59
def prefixEnd_1718935 : Nat := 4983230072969 + 3 ^ 40 * 1718935 * 2
def baseEnd_1718935 : Nat := 196142193074741642801615

theorem tailTrace_1718935 : CollatzResearch.WordTrace tailWord_1718935 prefixEnd_1718935 196142193074741642801615 := by
  unfold tailWord_1718935
  simp only [CollatzResearch.WordTrace]
  refine ⟨62694710027599540570750259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41796473351733027047166839 62694710027599540570750259)
  ·
    refine ⟨94042065041399310856125389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62694710027599540570750259 94042065041399310856125389)
    ·
      refine ⟨35265774390524741571047021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94042065041399310856125389 35265774390524741571047021)
      ·
        refine ⟨13224665396446778089142633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35265774390524741571047021 13224665396446778089142633)
        ·
          refine ⟨9918499047335083566856975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13224665396446778089142633 9918499047335083566856975)
          ·
            refine ⟨14877748571002625350285463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9918499047335083566856975 14877748571002625350285463)
            ·
              refine ⟨22316622856503938025428195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14877748571002625350285463 22316622856503938025428195)
              ·
                refine ⟨33474934284755907038142293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22316622856503938025428195 33474934284755907038142293)
                ·
                  refine ⟨196142193074741642801615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 33474934284755907038142293 196142193074741642801615)
                  ·
                    rfl

theorem cell22_1718935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 1, 9].length) (baseStart_1718935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1718935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1718935 prefixEnd_1718935 := by exact prefixLift 1718935
  have htrace : WordTrace (prefixWord ++ tailWord_1718935) baseStart_1718935 baseEnd_1718935 := by
    simpa [prefixWord, tailWord_1718935, baseEnd_1718935] using wordTrace_append hprefix tailTrace_1718935
  have hstable : (prefixWord ++ tailWord_1718935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1718935).length < 2 ^ (prefixWord ++ tailWord_1718935).sum := by decide
  have hdescent : baseEnd_1718935 < baseStart_1718935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1718935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719063 : List Nat := [1, 1, 3, 4, 3, 2, 1, 2, 2, 3]
def baseStart_1719063 : Nat := 118140960795 + 1719063 * 2 ^ 59
def prefixEnd_1719063 : Nat := 4983230072969 + 3 ^ 40 * 1719063 * 2
def baseEnd_1719063 : Nat := 588470396240075261204453

theorem tailTrace_1719063 : CollatzResearch.WordTrace tailWord_1719063 prefixEnd_1719063 588470396240075261204453 := by
  unfold tailWord_1719063
  simp only [CollatzResearch.WordTrace]
  refine ⟨62699378571135818431409843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41799585714090545620939895 62699378571135818431409843)
  ·
    refine ⟨94049067856703727647114765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62699378571135818431409843 94049067856703727647114765)
    ·
      refine ⟨35268400446263897867668037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 94049067856703727647114765 35268400446263897867668037)
      ·
        refine ⟨6612825083674480850187757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35268400446263897867668037 6612825083674480850187757)
        ·
          refine ⟨2479809406377930318820409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6612825083674480850187757 2479809406377930318820409)
          ·
            refine ⟨1859857054783447739115307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2479809406377930318820409 1859857054783447739115307)
            ·
              refine ⟨2789785582175171608672961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1859857054783447739115307 2789785582175171608672961)
              ·
                refine ⟨2092339186631378706504721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2789785582175171608672961 2092339186631378706504721)
                ·
                  refine ⟨1569254389973534029878541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2092339186631378706504721 1569254389973534029878541)
                  ·
                    refine ⟨588470396240075261204453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1569254389973534029878541 588470396240075261204453)
                    ·
                      rfl

theorem cell22_1719063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 2, 2, 3].length) (baseStart_1719063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719063 prefixEnd_1719063 := by exact prefixLift 1719063
  have htrace : WordTrace (prefixWord ++ tailWord_1719063) baseStart_1719063 baseEnd_1719063 := by
    simpa [prefixWord, tailWord_1719063, baseEnd_1719063] using wordTrace_append hprefix tailTrace_1719063
  have hstable : (prefixWord ++ tailWord_1719063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719063).length < 2 ^ (prefixWord ++ tailWord_1719063).sum := by decide
  have hdescent : baseEnd_1719063 < baseStart_1719063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719164 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 6, 3]
def baseStart_1719164 : Nat := 118140960795 + 1719164 * 2 ^ 59
def prefixEnd_1719164 : Nat := 4983230072969 + 3 ^ 40 * 1719164 * 2
def baseEnd_1719164 : Nat := 588504970604144664429143

theorem tailTrace_1719164 : CollatzResearch.WordTrace tailWord_1719164 prefixEnd_1719164 588504970604144664429143 := by
  unfold tailWord_1719164
  simp only [CollatzResearch.WordTrace]
  refine ⟨31351531171884956340418273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41802041562513275120557697 31351531171884956340418273)
  ·
    refine ⟨23513648378913717255313705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31351531171884956340418273 23513648378913717255313705)
    ·
      refine ⟨17635236284185287941485279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23513648378913717255313705 17635236284185287941485279)
      ·
        refine ⟨26452854426277931912227919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17635236284185287941485279 26452854426277931912227919)
        ·
          refine ⟨39679281639416897868341879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26452854426277931912227919 39679281639416897868341879)
          ·
            refine ⟨59518922459125346802512819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39679281639416897868341879 59518922459125346802512819)
            ·
              refine ⟨89278383688688020203769229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59518922459125346802512819 89278383688688020203769229)
              ·
                refine ⟨33479393883258007576413461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 89278383688688020203769229 33479393883258007576413461)
                ·
                  refine ⟨1569346588277719105144381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 33479393883258007576413461 1569346588277719105144381)
                  ·
                    refine ⟨588504970604144664429143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1569346588277719105144381 588504970604144664429143)
                    ·
                      rfl

theorem cell22_1719164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_1719164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719164 prefixEnd_1719164 := by exact prefixLift 1719164
  have htrace : WordTrace (prefixWord ++ tailWord_1719164) baseStart_1719164 baseEnd_1719164 := by
    simpa [prefixWord, tailWord_1719164, baseEnd_1719164] using wordTrace_append hprefix tailTrace_1719164
  have hstable : (prefixWord ++ tailWord_1719164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719164).length < 2 ^ (prefixWord ++ tailWord_1719164).sum := by decide
  have hdescent : baseEnd_1719164 < baseStart_1719164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719177 : List Nat := [1, 2, 1, 1, 5, 12]
def baseStart_1719177 : Nat := 118140960795 + 1719177 * 2 ^ 59
def prefixEnd_1719177 : Nat := 4983230072969 + 3 ^ 40 * 1719177 * 2
def baseEnd_1719177 : Nat := 7265548404565641529063

theorem tailTrace_1719177 : CollatzResearch.WordTrace tailWord_1719177 prefixEnd_1719177 7265548404565641529063 := by
  unfold tailWord_1719177
  simp only [CollatzResearch.WordTrace]
  refine ⟨62703536492722815901059785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41802357661815210600706523 62703536492722815901059785)
  ·
    refine ⟨47027652369542111925794839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62703536492722815901059785 47027652369542111925794839)
    ·
      refine ⟨70541478554313167888692259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47027652369542111925794839 70541478554313167888692259)
      ·
        refine ⟨105812217831469751833038389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70541478554313167888692259 105812217831469751833038389)
        ·
          refine ⟨9919895421700289234347349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105812217831469751833038389 9919895421700289234347349)
          ·
            refine ⟨7265548404565641529063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 9919895421700289234347349 7265548404565641529063)
            ·
              rfl

theorem cell22_1719177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 12].length) (baseStart_1719177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719177 prefixEnd_1719177 := by exact prefixLift 1719177
  have htrace : WordTrace (prefixWord ++ tailWord_1719177) baseStart_1719177 baseEnd_1719177 := by
    simpa [prefixWord, tailWord_1719177, baseEnd_1719177] using wordTrace_append hprefix tailTrace_1719177
  have hstable : (prefixWord ++ tailWord_1719177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719177).length < 2 ^ (prefixWord ++ tailWord_1719177).sum := by decide
  have hdescent : baseEnd_1719177 < baseStart_1719177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719179 : List Nat := [1, 1, 1, 1, 4, 2, 4, 2, 2, 4]
def baseStart_1719179 : Nat := 118140960795 + 1719179 * 2 ^ 59
def prefixEnd_1719179 : Nat := 4983230072969 + 3 ^ 40 * 1719179 * 2
def baseEnd_1719179 : Nat := 588510105410689625304097

theorem tailTrace_1719179 : CollatzResearch.WordTrace tailWord_1719179 prefixEnd_1719179 588510105410689625304097 := by
  unfold tailWord_1719179
  simp only [CollatzResearch.WordTrace]
  refine ⟨62703609438715570242632591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41802406292477046828421727 62703609438715570242632591)
  ·
    refine ⟨94055414158073355363948887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62703609438715570242632591 94055414158073355363948887)
    ·
      refine ⟨141083121237110033045923331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94055414158073355363948887 141083121237110033045923331)
      ·
        refine ⟨211624681855665049568884997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141083121237110033045923331 211624681855665049568884997)
        ·
          refine ⟨39679627847937196794165937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 211624681855665049568884997 39679627847937196794165937)
          ·
            refine ⟨29759720885952897595624453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39679627847937196794165937 29759720885952897595624453)
            ·
              refine ⟨5579947666116168299179585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29759720885952897595624453 5579947666116168299179585)
              ·
                refine ⟨4184960749587126224384689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5579947666116168299179585 4184960749587126224384689)
                ·
                  refine ⟨3138720562190344668288517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4184960749587126224384689 3138720562190344668288517)
                  ·
                    refine ⟨588510105410689625304097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3138720562190344668288517 588510105410689625304097)
                    ·
                      rfl

theorem cell22_1719179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 2, 2, 4].length) (baseStart_1719179 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719179 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719179 prefixEnd_1719179 := by exact prefixLift 1719179
  have htrace : WordTrace (prefixWord ++ tailWord_1719179) baseStart_1719179 baseEnd_1719179 := by
    simpa [prefixWord, tailWord_1719179, baseEnd_1719179] using wordTrace_append hprefix tailTrace_1719179
  have hstable : (prefixWord ++ tailWord_1719179).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719179).length < 2 ^ (prefixWord ++ tailWord_1719179).sum := by decide
  have hdescent : baseEnd_1719179 < baseStart_1719179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719213 : List Nat := [1, 5, 2, 3, 1, 1, 1, 1, 1, 6]
def baseStart_1719213 : Nat := 118140960795 + 1719213 * 2 ^ 59
def prefixEnd_1719213 : Nat := 4983230072969 + 3 ^ 40 * 1719213 * 2
def baseEnd_1719213 : Nat := 588521744305524869953993

theorem tailTrace_1719213 : CollatzResearch.WordTrace tailWord_1719213 prefixEnd_1719213 588521744305524869953993 := by
  unfold tailWord_1719213
  simp only [CollatzResearch.WordTrace]
  refine ⟨62704849520592394049370293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41803233013728262699580195 62704849520592394049370293)
  ·
    refine ⟨5878579642555536942128465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 62704849520592394049370293 5878579642555536942128465)
    ·
      refine ⟨4408934731916652706596349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5878579642555536942128465 4408934731916652706596349)
      ·
        refine ⟨1653350524468744764973631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4408934731916652706596349 1653350524468744764973631)
        ·
          refine ⟨2480025786703117147460447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1653350524468744764973631 2480025786703117147460447)
          ·
            refine ⟨3720038680054675721190671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480025786703117147460447 3720038680054675721190671)
            ·
              refine ⟨5580058020082013581786007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3720038680054675721190671 5580058020082013581786007)
              ·
                refine ⟨8370087030123020372679011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5580058020082013581786007 8370087030123020372679011)
                ·
                  refine ⟨12555130545184530559018517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8370087030123020372679011 12555130545184530559018517)
                  ·
                    refine ⟨588521744305524869953993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12555130545184530559018517 588521744305524869953993)
                    ·
                      rfl

theorem cell22_1719213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_1719213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719213 prefixEnd_1719213 := by exact prefixLift 1719213
  have htrace : WordTrace (prefixWord ++ tailWord_1719213) baseStart_1719213 baseEnd_1719213 := by
    simpa [prefixWord, tailWord_1719213, baseEnd_1719213] using wordTrace_append hprefix tailTrace_1719213
  have hstable : (prefixWord ++ tailWord_1719213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719213).length < 2 ^ (prefixWord ++ tailWord_1719213).sum := by decide
  have hdescent : baseEnd_1719213 < baseStart_1719213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719243 : List Nat := [1, 1, 1, 1, 3, 5, 2, 4, 1, 3]
def baseStart_1719243 : Nat := 118140960795 + 1719243 * 2 ^ 59
def prefixEnd_1719243 : Nat := 4983230072969 + 3 ^ 40 * 1719243 * 2
def baseEnd_1719243 : Nat := 588532013918614791703901

theorem tailTrace_1719243 : CollatzResearch.WordTrace tailWord_1719243 prefixEnd_1719243 588532013918614791703901 := by
  unfold tailWord_1719243
  simp only [CollatzResearch.WordTrace]
  refine ⟨62705943710483709172962383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41803962473655806115308255 62705943710483709172962383)
  ·
    refine ⟨94058915565725563759443575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62705943710483709172962383 94058915565725563759443575)
    ·
      refine ⟨141088373348588345639165363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94058915565725563759443575 141088373348588345639165363)
      ·
        refine ⟨211632560022882518458748045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 141088373348588345639165363 211632560022882518458748045)
        ·
          refine ⟨79362210008580944422030517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 211632560022882518458748045 79362210008580944422030517)
          ·
            refine ⟨7440207188304463539565361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 79362210008580944422030517 7440207188304463539565361)
            ·
              refine ⟨5580155391228347654674021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7440207188304463539565361 5580155391228347654674021)
              ·
                refine ⟨1046279135855315185251379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5580155391228347654674021 1046279135855315185251379)
                ·
                  refine ⟨1569418703782972777877069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046279135855315185251379 1569418703782972777877069)
                  ·
                    refine ⟨588532013918614791703901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1569418703782972777877069 588532013918614791703901)
                    ·
                      rfl

theorem cell22_1719243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 4, 1, 3].length) (baseStart_1719243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719243 prefixEnd_1719243 := by exact prefixLift 1719243
  have htrace : WordTrace (prefixWord ++ tailWord_1719243) baseStart_1719243 baseEnd_1719243 := by
    simpa [prefixWord, tailWord_1719243, baseEnd_1719243] using wordTrace_append hprefix tailTrace_1719243
  have hstable : (prefixWord ++ tailWord_1719243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719243).length < 2 ^ (prefixWord ++ tailWord_1719243).sum := by decide
  have hdescent : baseEnd_1719243 < baseStart_1719243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719294 : List Nat := [4, 2, 2, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1719294 : Nat := 118140960795 + 1719294 * 2 ^ 59
def prefixEnd_1719294 : Nat := 4983230072969 + 3 ^ 40 * 1719294 * 2
def baseEnd_1719294 : Nat := 588549472260867658678745

theorem tailTrace_1719294 : CollatzResearch.WordTrace tailWord_1719294 prefixEnd_1719294 588549472260867658678745 := by
  unfold tailWord_1719294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7838475479162368110383617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41805202555532629922045957 7838475479162368110383617)
  ·
    refine ⟨5878856609371776082787713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7838475479162368110383617 5878856609371776082787713)
    ·
      refine ⟨4409142457028832062090785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5878856609371776082787713 4409142457028832062090785)
      ·
        refine ⟨3306856842771624046568089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4409142457028832062090785 3306856842771624046568089)
        ·
          refine ⟨2480142632078718034926067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3306856842771624046568089 2480142632078718034926067)
          ·
            refine ⟨3720213948118077052389101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2480142632078718034926067 3720213948118077052389101)
            ·
              refine ⟨1395080230544278894645913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3720213948118077052389101 1395080230544278894645913)
              ·
                refine ⟨1046310172908209170984435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1395080230544278894645913 1046310172908209170984435)
                ·
                  refine ⟨1569465259362313756476653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1046310172908209170984435 1569465259362313756476653)
                  ·
                    refine ⟨588549472260867658678745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1569465259362313756476653 588549472260867658678745)
                    ·
                      rfl

theorem cell22_1719294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1719294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719294 prefixEnd_1719294 := by exact prefixLift 1719294
  have htrace : WordTrace (prefixWord ++ tailWord_1719294) baseStart_1719294 baseEnd_1719294 := by
    simpa [prefixWord, tailWord_1719294, baseEnd_1719294] using wordTrace_append hprefix tailTrace_1719294
  have hstable : (prefixWord ++ tailWord_1719294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719294).length < 2 ^ (prefixWord ++ tailWord_1719294).sum := by decide
  have hdescent : baseEnd_1719294 < baseStart_1719294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719331 : List Nat := [1, 1, 1, 4, 3, 2, 1, 3, 2, 4]
def baseStart_1719331 : Nat := 118140960795 + 1719331 * 2 ^ 59
def prefixEnd_1719331 : Nat := 4983230072969 + 3 ^ 40 * 1719331 * 2
def baseEnd_1719331 : Nat := 588562138117011895503631

theorem tailTrace_1719331 : CollatzResearch.WordTrace tailWord_1719331 prefixEnd_1719331 588562138117011895503631 := by
  unfold tailWord_1719331
  simp only [CollatzResearch.WordTrace]
  refine ⟨62709153334164900202165847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41806102222776600134777231 62709153334164900202165847)
  ·
    refine ⟨94063730001247350303248771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62709153334164900202165847 94063730001247350303248771)
    ·
      refine ⟨141095595001871025454873157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94063730001247350303248771 141095595001871025454873157)
      ·
        refine ⟨26455424062850817272788717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 141095595001871025454873157 26455424062850817272788717)
        ·
          refine ⟨9920784023569056477295769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26455424062850817272788717 9920784023569056477295769)
          ·
            refine ⟨7440588017676792357971827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9920784023569056477295769 7440588017676792357971827)
            ·
              refine ⟨11160882026515188536957741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440588017676792357971827 11160882026515188536957741)
              ·
                refine ⟨4185330759943195701359153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11160882026515188536957741 4185330759943195701359153)
                ·
                  refine ⟨3138998069957396776019365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4185330759943195701359153 3138998069957396776019365)
                  ·
                    refine ⟨588562138117011895503631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3138998069957396776019365 588562138117011895503631)
                    ·
                      rfl

theorem cell22_1719331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 3, 2, 4].length) (baseStart_1719331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719331 prefixEnd_1719331 := by exact prefixLift 1719331
  have htrace : WordTrace (prefixWord ++ tailWord_1719331) baseStart_1719331 baseEnd_1719331 := by
    simpa [prefixWord, tailWord_1719331, baseEnd_1719331] using wordTrace_append hprefix tailTrace_1719331
  have hstable : (prefixWord ++ tailWord_1719331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719331).length < 2 ^ (prefixWord ++ tailWord_1719331).sum := by decide
  have hdescent : baseEnd_1719331 < baseStart_1719331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719350 : List Nat := [5, 1, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_1719350 : Nat := 118140960795 + 1719350 * 2 ^ 59
def prefixEnd_1719350 : Nat := 4983230072969 + 3 ^ 40 * 1719350 * 2
def baseEnd_1719350 : Nat := 588568642205302179278573

theorem tailTrace_1719350 : CollatzResearch.WordTrace tailWord_1719350 prefixEnd_1719350 588568642205302179278573 := by
  unfold tailWord_1719350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3919365395068504152944219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41806564214064044298071669 3919365395068504152944219)
  ·
    refine ⟨5879048092602756229416329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3919365395068504152944219 5879048092602756229416329)
    ·
      refine ⟨4409286069452067172062247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5879048092602756229416329 4409286069452067172062247)
      ·
        refine ⟨6613929104178100758093371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4409286069452067172062247 6613929104178100758093371)
        ·
          refine ⟨9920893656267151137140057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6613929104178100758093371 9920893656267151137140057)
          ·
            refine ⟨7440670242200363352855043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9920893656267151137140057 7440670242200363352855043)
            ·
              refine ⟨11161005363300545029282565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440670242200363352855043 11161005363300545029282565)
              ·
                refine ⟨2092688505618852192990481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 11161005363300545029282565 2092688505618852192990481)
                ·
                  refine ⟨1569516379214139144742861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2092688505618852192990481 1569516379214139144742861)
                  ·
                    refine ⟨588568642205302179278573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1569516379214139144742861 588568642205302179278573)
                    ·
                      rfl

theorem cell22_1719350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_1719350 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719350 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719350 prefixEnd_1719350 := by exact prefixLift 1719350
  have htrace : WordTrace (prefixWord ++ tailWord_1719350) baseStart_1719350 baseEnd_1719350 := by
    simpa [prefixWord, tailWord_1719350, baseEnd_1719350] using wordTrace_append hprefix tailTrace_1719350
  have hstable : (prefixWord ++ tailWord_1719350).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719350).length < 2 ^ (prefixWord ++ tailWord_1719350).sum := by decide
  have hdescent : baseEnd_1719350 < baseStart_1719350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719378 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 5, 3]
def baseStart_1719378 : Nat := 118140960795 + 1719378 * 2 ^ 59
def prefixEnd_1719378 : Nat := 4983230072969 + 3 ^ 40 * 1719378 * 2
def baseEnd_1719378 : Nat := 588578227177519439578487

theorem tailTrace_1719378 : CollatzResearch.WordTrace tailWord_1719378 prefixEnd_1719378 588578227177519439578487 := by
  unfold tailWord_1719378
  simp only [CollatzResearch.WordTrace]
  refine ⟨15677716891248656807281697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41807245043329751486084525 15677716891248656807281697)
  ·
    refine ⟨11758287668436492605461273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15677716891248656807281697 11758287668436492605461273)
    ·
      refine ⟨8818715751327369454095955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11758287668436492605461273 8818715751327369454095955)
      ·
        refine ⟨13228073626991054181143933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8818715751327369454095955 13228073626991054181143933)
        ·
          refine ⟨4960527610121645317928975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13228073626991054181143933 4960527610121645317928975)
          ·
            refine ⟨7440791415182467976893463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4960527610121645317928975 7440791415182467976893463)
            ·
              refine ⟨11161187122773701965340195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7440791415182467976893463 11161187122773701965340195)
              ·
                refine ⟨16741780684160552948010293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11161187122773701965340195 16741780684160552948010293)
                ·
                  refine ⟨1569541939140051838875965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16741780684160552948010293 1569541939140051838875965)
                  ·
                    refine ⟨588578227177519439578487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1569541939140051838875965 588578227177519439578487)
                    ·
                      rfl

theorem cell22_1719378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 5, 3].length) (baseStart_1719378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719378 prefixEnd_1719378 := by exact prefixLift 1719378
  have htrace : WordTrace (prefixWord ++ tailWord_1719378) baseStart_1719378 baseEnd_1719378 := by
    simpa [prefixWord, tailWord_1719378, baseEnd_1719378] using wordTrace_append hprefix tailTrace_1719378
  have hstable : (prefixWord ++ tailWord_1719378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719378).length < 2 ^ (prefixWord ++ tailWord_1719378).sum := by decide
  have hdescent : baseEnd_1719378 < baseStart_1719378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719425 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 5]
def baseStart_1719425 : Nat := 118140960795 + 1719425 * 2 ^ 59
def prefixEnd_1719425 : Nat := 4983230072969 + 3 ^ 40 * 1719425 * 2
def baseEnd_1719425 : Nat := 196198105412675661217781

theorem tailTrace_1719425 : CollatzResearch.WordTrace tailWord_1719425 prefixEnd_1719425 196198105412675661217781 := by
  unfold tailWord_1719425
  simp only [CollatzResearch.WordTrace]
  refine ⟨62712581795824354256087729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41808387863882902837391819 62712581795824354256087729)
  ·
    refine ⟨47034436346868265692065797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62712581795824354256087729 47034436346868265692065797)
    ·
      refine ⟨8818956815037799817262337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 47034436346868265692065797 8818956815037799817262337)
      ·
        refine ⟨6614217611278349862946753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8818956815037799817262337 6614217611278349862946753)
        ·
          refine ⟨4960663208458762397210065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6614217611278349862946753 4960663208458762397210065)
          ·
            refine ⟨3720497406344071797907549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4960663208458762397210065 3720497406344071797907549)
            ·
              refine ⟨1395186527379026924215331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3720497406344071797907549 1395186527379026924215331)
              ·
                refine ⟨2092779791068540386322997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395186527379026924215331 2092779791068540386322997)
                ·
                  refine ⟨196198105412675661217781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2092779791068540386322997 196198105412675661217781)
                  ·
                    rfl

theorem cell22_1719425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 5].length) (baseStart_1719425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719425 prefixEnd_1719425 := by exact prefixLift 1719425
  have htrace : WordTrace (prefixWord ++ tailWord_1719425) baseStart_1719425 baseEnd_1719425 := by
    simpa [prefixWord, tailWord_1719425, baseEnd_1719425] using wordTrace_append hprefix tailTrace_1719425
  have hstable : (prefixWord ++ tailWord_1719425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719425).length < 2 ^ (prefixWord ++ tailWord_1719425).sum := by decide
  have hdescent : baseEnd_1719425 < baseStart_1719425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719481 : List Nat := [1, 2, 1, 4, 1, 3, 1, 9]
def baseStart_1719481 : Nat := 118140960795 + 1719481 * 2 ^ 59
def prefixEnd_1719481 : Nat := 4983230072969 + 3 ^ 40 * 1719481 * 2
def baseEnd_1719481 : Nat := 65401498464717944917019

theorem tailTrace_1719481 : CollatzResearch.WordTrace tailWord_1719481 prefixEnd_1719481 65401498464717944917019 := by
  unfold tailWord_1719481
  simp only [CollatzResearch.WordTrace]
  refine ⟨62714624283621475820126297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41809749522414317213417531 62714624283621475820126297)
  ·
    refine ⟨47035968212716106865094723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62714624283621475820126297 47035968212716106865094723)
    ·
      refine ⟨70553952319074160297642085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 47035968212716106865094723 70553952319074160297642085)
      ·
        refine ⟨13228866059826405055807891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70553952319074160297642085 13228866059826405055807891)
        ·
          refine ⟨19843299089739607583711837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13228866059826405055807891 19843299089739607583711837)
          ·
            refine ⟨7441237158652352843891939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19843299089739607583711837 7441237158652352843891939)
            ·
              refine ⟨11161855737978529265837909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7441237158652352843891939 11161855737978529265837909)
              ·
                refine ⟨65401498464717944917019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 11161855737978529265837909 65401498464717944917019)
                ·
                  rfl

theorem cell22_1719481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 9].length) (baseStart_1719481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719481 prefixEnd_1719481 := by exact prefixLift 1719481
  have htrace : WordTrace (prefixWord ++ tailWord_1719481) baseStart_1719481 baseEnd_1719481 := by
    simpa [prefixWord, tailWord_1719481, baseEnd_1719481] using wordTrace_append hprefix tailTrace_1719481
  have hstable : (prefixWord ++ tailWord_1719481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719481).length < 2 ^ (prefixWord ++ tailWord_1719481).sum := by decide
  have hdescent : baseEnd_1719481 < baseStart_1719481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719496 : List Nat := [2, 1, 3, 1, 2, 1, 2, 1, 2, 7]
def baseStart_1719496 : Nat := 118140960795 + 1719496 * 2 ^ 59
def prefixEnd_1719496 : Nat := 4983230072969 + 3 ^ 40 * 1719496 * 2
def baseEnd_1719496 : Nat := 588618620989006465128125

theorem tailTrace_1719496 : CollatzResearch.WordTrace tailWord_1719496 prefixEnd_1719496 588618620989006465128125 := by
  unfold tailWord_1719496
  simp only [CollatzResearch.WordTrace]
  refine ⟨31357585689283566690961171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41810114252378088921281561 31357585689283566690961171)
  ·
    refine ⟨47036378533925350036441757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31357585689283566690961171 47036378533925350036441757)
    ·
      refine ⟨17638641950222006263665659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 47036378533925350036441757 17638641950222006263665659)
      ·
        refine ⟨26457962925333009395498489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17638641950222006263665659 26457962925333009395498489)
        ·
          refine ⟨19843472193999757046623867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26457962925333009395498489 19843472193999757046623867)
          ·
            refine ⟨29765208290999635569935801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19843472193999757046623867 29765208290999635569935801)
            ·
              refine ⟨22323906218249726677451851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29765208290999635569935801 22323906218249726677451851)
              ·
                refine ⟨33485859327374590016177777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22323906218249726677451851 33485859327374590016177777)
                ·
                  refine ⟨25114394495530942512133333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33485859327374590016177777 25114394495530942512133333)
                  ·
                    refine ⟨588618620989006465128125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 25114394495530942512133333 588618620989006465128125)
                    ·
                      rfl

theorem cell22_1719496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_1719496 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719496 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719496 prefixEnd_1719496 := by exact prefixLift 1719496
  have htrace : WordTrace (prefixWord ++ tailWord_1719496) baseStart_1719496 baseEnd_1719496 := by
    simpa [prefixWord, tailWord_1719496, baseEnd_1719496] using wordTrace_append hprefix tailTrace_1719496
  have hstable : (prefixWord ++ tailWord_1719496).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719496).length < 2 ^ (prefixWord ++ tailWord_1719496).sum := by decide
  have hdescent : baseEnd_1719496 < baseStart_1719496 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719650 : List Nat := [3, 3, 2, 1, 1, 1, 4, 7]
def baseStart_1719650 : Nat := 118140960795 + 1719650 * 2 ^ 59
def prefixEnd_1719650 : Nat := 4983230072969 + 3 ^ 40 * 1719650 * 2
def baseEnd_1719650 : Nat := 65407926481800155197517

theorem tailTrace_1719650 : CollatzResearch.WordTrace tailWord_1719650 prefixEnd_1719650 65407926481800155197517 := by
  unfold tailWord_1719650
  simp only [CollatzResearch.WordTrace]
  refine ⟨15680197055002304420757101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41813858813339478455352269 15680197055002304420757101)
  ·
    refine ⟨5880073895625864157783913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15680197055002304420757101 5880073895625864157783913)
    ·
      refine ⟨4410055421719398118337935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5880073895625864157783913 4410055421719398118337935)
      ·
        refine ⟨6615083132579097177506903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4410055421719398118337935 6615083132579097177506903)
        ·
          refine ⟨9922624698868645766260355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6615083132579097177506903 9922624698868645766260355)
          ·
            refine ⟨14883937048302968649390533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9922624698868645766260355 14883937048302968649390533)
            ·
              refine ⟨2790738196556806621760725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14883937048302968649390533 2790738196556806621760725)
              ·
                refine ⟨65407926481800155197517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2790738196556806621760725 65407926481800155197517)
                ·
                  rfl

theorem cell22_1719650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 7].length) (baseStart_1719650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719650 prefixEnd_1719650 := by exact prefixLift 1719650
  have htrace : WordTrace (prefixWord ++ tailWord_1719650) baseStart_1719650 baseEnd_1719650 := by
    simpa [prefixWord, tailWord_1719650, baseEnd_1719650] using wordTrace_append hprefix tailTrace_1719650
  have hstable : (prefixWord ++ tailWord_1719650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719650).length < 2 ^ (prefixWord ++ tailWord_1719650).sum := by decide
  have hdescent : baseEnd_1719650 < baseStart_1719650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719665 : List Nat := [1, 2, 2, 2, 1, 2, 2, 4, 3, 3]
def baseStart_1719665 : Nat := 118140960795 + 1719665 * 2 ^ 59
def prefixEnd_1719665 : Nat := 4983230072969 + 3 ^ 40 * 1719665 * 2
def baseEnd_1719665 : Nat := 588676473142746357652607

theorem tailTrace_1719665 : CollatzResearch.WordTrace tailWord_1719665 prefixEnd_1719665 588676473142746357652607 := by
  unfold tailWord_1719665
  simp only [CollatzResearch.WordTrace]
  refine ⟨62721335314954875244824449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41814223543303250163216299 62721335314954875244824449)
  ·
    refine ⟨47041001486216156433618337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62721335314954875244824449 47041001486216156433618337)
    ·
      refine ⟨35280751114662117325213753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 47041001486216156433618337 35280751114662117325213753)
      ·
        refine ⟨26460563335996587993910315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35280751114662117325213753 26460563335996587993910315)
        ·
          refine ⟨39690845003994881990865473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26460563335996587993910315 39690845003994881990865473)
          ·
            refine ⟨29768133752996161493149105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39690845003994881990865473 29768133752996161493149105)
            ·
              refine ⟨22326100314747121119861829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29768133752996161493149105 22326100314747121119861829)
              ·
                refine ⟨4186143809015085209974093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22326100314747121119861829 4186143809015085209974093)
                ·
                  refine ⟨1569803928380656953740285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4186143809015085209974093 1569803928380656953740285)
                  ·
                    refine ⟨588676473142746357652607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1569803928380656953740285 588676473142746357652607)
                    ·
                      rfl

theorem cell22_1719665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 4, 3, 3].length) (baseStart_1719665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719665 prefixEnd_1719665 := by exact prefixLift 1719665
  have htrace : WordTrace (prefixWord ++ tailWord_1719665) baseStart_1719665 baseEnd_1719665 := by
    simpa [prefixWord, tailWord_1719665, baseEnd_1719665] using wordTrace_append hprefix tailTrace_1719665
  have hstable : (prefixWord ++ tailWord_1719665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719665).length < 2 ^ (prefixWord ++ tailWord_1719665).sum := by decide
  have hdescent : baseEnd_1719665 < baseStart_1719665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719770 : List Nat := [3, 1, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_1719770 : Nat := 118140960795 + 1719770 * 2 ^ 59
def prefixEnd_1719770 : Nat := 4983230072969 + 3 ^ 40 * 1719770 * 2
def baseEnd_1719770 : Nat := 588712416788561083777285

theorem tailTrace_1719770 : CollatzResearch.WordTrace tailWord_1719770 prefixEnd_1719770 588712416788561083777285 := by
  unfold tailWord_1719770
  simp only [CollatzResearch.WordTrace]
  refine ⟨15681291244893619544349191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41816776653049652118264509 15681291244893619544349191)
  ·
    refine ⟨23521936867340429316523787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15681291244893619544349191 23521936867340429316523787)
    ·
      refine ⟨35282905301010643974785681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23521936867340429316523787 35282905301010643974785681)
      ·
        refine ⟨26462178975757982981089261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35282905301010643974785681 26462178975757982981089261)
        ·
          refine ⟨9923317115909243617908473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26462178975757982981089261 9923317115909243617908473)
          ·
            refine ⟨7442487836931932713431355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9923317115909243617908473 7442487836931932713431355)
            ·
              refine ⟨11163731755397899070147033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7442487836931932713431355 11163731755397899070147033)
              ·
                refine ⟨8372798816548424302610275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11163731755397899070147033 8372798816548424302610275)
                ·
                  refine ⟨12559198224822636453915413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8372798816548424302610275 12559198224822636453915413)
                  ·
                    refine ⟨588712416788561083777285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12559198224822636453915413 588712416788561083777285)
                    ·
                      rfl

theorem cell22_1719770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_1719770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719770 prefixEnd_1719770 := by exact prefixLift 1719770
  have htrace : WordTrace (prefixWord ++ tailWord_1719770) baseStart_1719770 baseEnd_1719770 := by
    simpa [prefixWord, tailWord_1719770, baseEnd_1719770] using wordTrace_append hprefix tailTrace_1719770
  have hstable : (prefixWord ++ tailWord_1719770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719770).length < 2 ^ (prefixWord ++ tailWord_1719770).sum := by decide
  have hdescent : baseEnd_1719770 < baseStart_1719770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719845 : List Nat := [1, 3, 1, 2, 2, 1, 1, 2, 4, 5]
def baseStart_1719845 : Nat := 118140960795 + 1719845 * 2 ^ 59
def prefixEnd_1719845 : Nat := 4983230072969 + 3 ^ 40 * 1719845 * 2
def baseEnd_1719845 : Nat := 588738090821285888152055

theorem tailTrace_1719845 : CollatzResearch.WordTrace tailWord_1719845 prefixEnd_1719845 588738090821285888152055 := by
  unfold tailWord_1719845
  simp only [CollatzResearch.WordTrace]
  refine ⟨62727900454302765986376989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41818600302868510657584659 62727900454302765986376989)
  ·
    refine ⟨23522962670363537244891371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62727900454302765986376989 23522962670363537244891371)
    ·
      refine ⟨35284444005545305867337057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23522962670363537244891371 35284444005545305867337057)
      ·
        refine ⟨26463333004158979400502793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35284444005545305867337057 26463333004158979400502793)
        ·
          refine ⟨19847499753119234550377095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26463333004158979400502793 19847499753119234550377095)
          ·
            refine ⟨29771249629678851825565643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19847499753119234550377095 29771249629678851825565643)
            ·
              refine ⟨44656874444518277738348465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29771249629678851825565643 44656874444518277738348465)
              ·
                refine ⟨33492655833388708303761349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44656874444518277738348465 33492655833388708303761349)
                ·
                  refine ⟨6279872968760382806955253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33492655833388708303761349 6279872968760382806955253)
                  ·
                    refine ⟨588738090821285888152055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6279872968760382806955253 588738090821285888152055)
                    ·
                      rfl

theorem cell22_1719845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_1719845 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719845 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719845 prefixEnd_1719845 := by exact prefixLift 1719845
  have htrace : WordTrace (prefixWord ++ tailWord_1719845) baseStart_1719845 baseEnd_1719845 := by
    simpa [prefixWord, tailWord_1719845, baseEnd_1719845] using wordTrace_append hprefix tailTrace_1719845
  have hstable : (prefixWord ++ tailWord_1719845).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719845).length < 2 ^ (prefixWord ++ tailWord_1719845).sum := by decide
  have hdescent : baseEnd_1719845 < baseStart_1719845 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719892 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 6]
def baseStart_1719892 : Nat := 118140960795 + 1719892 * 2 ^ 59
def prefixEnd_1719892 : Nat := 4983230072969 + 3 ^ 40 * 1719892 * 2
def baseEnd_1719892 : Nat := 196251393293931144075637

theorem tailTrace_1719892 : CollatzResearch.WordTrace tailWord_1719892 prefixEnd_1719892 196251393293931144075637 := by
  unfold tailWord_1719892
  simp only [CollatzResearch.WordTrace]
  refine ⟨31364807342566246506668965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41819743123421662008891953 31364807342566246506668965)
  ·
    refine ⟨5880901376731171220000431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 31364807342566246506668965 5880901376731171220000431)
    ·
      refine ⟨8821352065096756830000647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5880901376731171220000431 8821352065096756830000647)
      ·
        refine ⟨13232028097645135245000971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8821352065096756830000647 13232028097645135245000971)
        ·
          refine ⟨19848042146467702867501457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13232028097645135245000971 19848042146467702867501457)
          ·
            refine ⟨14886031609850777150626093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19848042146467702867501457 14886031609850777150626093)
            ·
              refine ⟨5582261853694041431484785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14886031609850777150626093 5582261853694041431484785)
              ·
                refine ⟨4186696390270531073613589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5582261853694041431484785 4186696390270531073613589)
                ·
                  refine ⟨196251393293931144075637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4186696390270531073613589 196251393293931144075637)
                  ·
                    rfl

theorem cell22_1719892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_1719892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719892 prefixEnd_1719892 := by exact prefixLift 1719892
  have htrace : WordTrace (prefixWord ++ tailWord_1719892) baseStart_1719892 baseEnd_1719892 := by
    simpa [prefixWord, tailWord_1719892, baseEnd_1719892] using wordTrace_append hprefix tailTrace_1719892
  have hstable : (prefixWord ++ tailWord_1719892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719892).length < 2 ^ (prefixWord ++ tailWord_1719892).sum := by decide
  have hdescent : baseEnd_1719892 < baseStart_1719892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719907 : List Nat := [1, 1, 1, 5, 1, 3, 2, 2, 1, 5]
def baseStart_1719907 : Nat := 118140960795 + 1719907 * 2 ^ 59
def prefixEnd_1719907 : Nat := 4983230072969 + 3 ^ 40 * 1719907 * 2
def baseEnd_1719907 : Nat := 588759314688338393101865

theorem tailTrace_1719907 : CollatzResearch.WordTrace tailWord_1719907 prefixEnd_1719907 588759314688338393101865 := by
  unfold tailWord_1719907
  simp only [CollatzResearch.WordTrace]
  refine ⟨62730161780078150575133975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41820107853385433716755983 62730161780078150575133975)
  ·
    refine ⟨94095242670117225862700963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62730161780078150575133975 94095242670117225862700963)
    ·
      refine ⟨141142864005175838794051445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 94095242670117225862700963 141142864005175838794051445)
      ·
        refine ⟨13232143500485234886942323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 141142864005175838794051445 13232143500485234886942323)
        ·
          refine ⟨19848215250727852330413485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13232143500485234886942323 19848215250727852330413485)
          ·
            refine ⟨7443080719022944623905057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19848215250727852330413485 7443080719022944623905057)
            ·
              refine ⟨5582310539267208467928793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7443080719022944623905057 5582310539267208467928793)
              ·
                refine ⟨4186732904450406350946595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5582310539267208467928793 4186732904450406350946595)
                ·
                  refine ⟨6280099356675609526419893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4186732904450406350946595 6280099356675609526419893)
                  ·
                    refine ⟨588759314688338393101865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6280099356675609526419893 588759314688338393101865)
                    ·
                      rfl

theorem cell22_1719907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 2, 1, 5].length) (baseStart_1719907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719907 prefixEnd_1719907 := by exact prefixLift 1719907
  have htrace : WordTrace (prefixWord ++ tailWord_1719907) baseStart_1719907 baseEnd_1719907 := by
    simpa [prefixWord, tailWord_1719907, baseEnd_1719907] using wordTrace_append hprefix tailTrace_1719907
  have hstable : (prefixWord ++ tailWord_1719907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719907).length < 2 ^ (prefixWord ++ tailWord_1719907).sum := by decide
  have hdescent : baseEnd_1719907 < baseStart_1719907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719909 : List Nat := [1, 3, 1, 3, 3, 1, 1, 5, 4]
def baseStart_1719909 : Nat := 118140960795 + 1719909 * 2 ^ 59
def prefixEnd_1719909 : Nat := 4983230072969 + 3 ^ 40 * 1719909 * 2
def baseEnd_1719909 : Nat := 196253333109737018183953

theorem tailTrace_1719909 : CollatzResearch.WordTrace tailWord_1719909 prefixEnd_1719909 196253333109737018183953 := by
  unfold tailWord_1719909
  simp only [CollatzResearch.WordTrace]
  refine ⟨62730234726070904916706781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41820156484047269944471187 62730234726070904916706781)
  ·
    refine ⟨23523838022276589343765043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62730234726070904916706781 23523838022276589343765043)
    ·
      refine ⟨35285757033414884015647565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23523838022276589343765043 35285757033414884015647565)
      ·
        refine ⟨13232158887530581505867837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35285757033414884015647565 13232158887530581505867837)
        ·
          refine ⟨4962059582823968064700439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13232158887530581505867837 4962059582823968064700439)
          ·
            refine ⟨7443089374235952097050659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962059582823968064700439 7443089374235952097050659)
            ·
              refine ⟨11164634061353928145575989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7443089374235952097050659 11164634061353928145575989)
              ·
                refine ⟨1046684443251930763647749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 11164634061353928145575989 1046684443251930763647749)
                ·
                  refine ⟨196253333109737018183953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1046684443251930763647749 196253333109737018183953)
                  ·
                    rfl

theorem cell22_1719909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 4].length) (baseStart_1719909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719909 prefixEnd_1719909 := by exact prefixLift 1719909
  have htrace : WordTrace (prefixWord ++ tailWord_1719909) baseStart_1719909 baseEnd_1719909 := by
    simpa [prefixWord, tailWord_1719909, baseEnd_1719909] using wordTrace_append hprefix tailTrace_1719909
  have hstable : (prefixWord ++ tailWord_1719909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719909).length < 2 ^ (prefixWord ++ tailWord_1719909).sum := by decide
  have hdescent : baseEnd_1719909 < baseStart_1719909 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719926 : List Nat := [5, 1, 1, 2, 2, 1, 2, 4, 4]
def baseStart_1719926 : Nat := 118140960795 + 1719926 * 2 ^ 59
def prefixEnd_1719926 : Nat := 4983230072969 + 3 ^ 40 * 1719926 * 2
def baseEnd_1719926 : Nat := 196255272925542892292269

theorem tailTrace_1719926 : CollatzResearch.WordTrace tailWord_1719926 prefixEnd_1719926 196255272925542892292269 := by
  unfold tailWord_1719926
  simp only [CollatzResearch.WordTrace]
  refine ⟨3920678422938082301254727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41820569844672877880050421 3920678422938082301254727)
  ·
    refine ⟨5881017634407123451882091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3920678422938082301254727 5881017634407123451882091)
    ·
      refine ⟨8821526451610685177823137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5881017634407123451882091 8821526451610685177823137)
      ·
        refine ⟨6616144838708013883367353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8821526451610685177823137 6616144838708013883367353)
        ·
          refine ⟨4962108629031010412525515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6616144838708013883367353 4962108629031010412525515)
          ·
            refine ⟨7443162943546515618788273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4962108629031010412525515 7443162943546515618788273)
            ·
              refine ⟨5582372207659886714091205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7443162943546515618788273 5582372207659886714091205)
              ·
                refine ⟨1046694788936228758892101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5582372207659886714091205 1046694788936228758892101)
                ·
                  refine ⟨196255272925542892292269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1046694788936228758892101 196255272925542892292269)
                  ·
                    rfl

theorem cell22_1719926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_1719926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719926 prefixEnd_1719926 := by exact prefixLift 1719926
  have htrace : WordTrace (prefixWord ++ tailWord_1719926) baseStart_1719926 baseEnd_1719926 := by
    simpa [prefixWord, tailWord_1719926, baseEnd_1719926] using wordTrace_append hprefix tailTrace_1719926
  have hstable : (prefixWord ++ tailWord_1719926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719926).length < 2 ^ (prefixWord ++ tailWord_1719926).sum := by decide
  have hdescent : baseEnd_1719926 < baseStart_1719926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1719941 : List Nat := [1, 3, 1, 1, 4, 1, 5, 1, 2, 3]
def baseStart_1719941 : Nat := 118140960795 + 1719941 * 2 ^ 59
def prefixEnd_1719941 : Nat := 4983230072969 + 3 ^ 40 * 1719941 * 2
def baseEnd_1719941 : Nat := 588770953583173637751761

theorem tailTrace_1719941 : CollatzResearch.WordTrace tailWord_1719941 prefixEnd_1719941 588770953583173637751761 := by
  unfold tailWord_1719941
  simp only [CollatzResearch.WordTrace]
  refine ⟨62731401861954974381871677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41820934574636649587914451 62731401861954974381871677)
  ·
    refine ⟨23524275698233115393201879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62731401861954974381871677 23524275698233115393201879)
    ·
      refine ⟨35286413547349673089802819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23524275698233115393201879 35286413547349673089802819)
      ·
        refine ⟨52929620321024509634704229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35286413547349673089802819 52929620321024509634704229)
        ·
          refine ⟨9924303810192095556507043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52929620321024509634704229 9924303810192095556507043)
          ·
            refine ⟨14886455715288143334760565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9924303810192095556507043 14886455715288143334760565)
            ·
              refine ⟨1395605223308263437633803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14886455715288143334760565 1395605223308263437633803)
              ·
                refine ⟨2093407834962395156450705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1395605223308263437633803 2093407834962395156450705)
                ·
                  refine ⟨1570055876221796367338029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2093407834962395156450705 1570055876221796367338029)
                  ·
                    refine ⟨588770953583173637751761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1570055876221796367338029 588770953583173637751761)
                    ·
                      rfl

theorem cell22_1719941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_1719941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1719941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1719941 prefixEnd_1719941 := by exact prefixLift 1719941
  have htrace : WordTrace (prefixWord ++ tailWord_1719941) baseStart_1719941 baseEnd_1719941 := by
    simpa [prefixWord, tailWord_1719941, baseEnd_1719941] using wordTrace_append hprefix tailTrace_1719941
  have hstable : (prefixWord ++ tailWord_1719941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1719941).length < 2 ^ (prefixWord ++ tailWord_1719941).sum := by decide
  have hdescent : baseEnd_1719941 < baseStart_1719941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1719941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
