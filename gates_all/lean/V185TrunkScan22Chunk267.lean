import V185TrunkScan22Chunk266

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2380255 : List Nat := [1, 1, 2, 3, 3, 2, 3, 2, 1, 4]
def baseStart_2380255 : Nat := 118140960795 + 2380255 * 2 ^ 59
def prefixEnd_2380255 : Nat := 4983230072969 + 3 ^ 40 * 2380255 * 2
def baseEnd_2380255 : Nat := 814809930178459983377275

theorem tailTrace_2380255 : CollatzResearch.WordTrace tailWord_2380255 prefixEnd_2380255 814809930178459983377275 := by
  unfold tailWord_2380255
  simp only [CollatzResearch.WordTrace]
  refine ⟨86815031991750125034782219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57876687994500083356521479 86815031991750125034782219)
  ·
    refine ⟨130222547987625187552173329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86815031991750125034782219 130222547987625187552173329)
    ·
      refine ⟨97666910990718890664129997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130222547987625187552173329 97666910990718890664129997)
      ·
        refine ⟨36625091621519583999048749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97666910990718890664129997 36625091621519583999048749)
        ·
          refine ⟨13734409358069843999643281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36625091621519583999048749 13734409358069843999643281)
          ·
            refine ⟨10300807018552382999732461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13734409358069843999643281 10300807018552382999732461)
            ·
              refine ⟨3862802631957143624899673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10300807018552382999732461 3862802631957143624899673)
              ·
                refine ⟨2897101973967857718674755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3862802631957143624899673 2897101973967857718674755)
                ·
                  refine ⟨4345652960951786578012133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2897101973967857718674755 4345652960951786578012133)
                  ·
                    refine ⟨814809930178459983377275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4345652960951786578012133 814809930178459983377275)
                    ·
                      rfl

theorem cell22_2380255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_2380255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380255 prefixEnd_2380255 := by exact prefixLift 2380255
  have htrace : WordTrace (prefixWord ++ tailWord_2380255) baseStart_2380255 baseEnd_2380255 := by
    simpa [prefixWord, tailWord_2380255, baseEnd_2380255] using wordTrace_append hprefix tailTrace_2380255
  have hstable : (prefixWord ++ tailWord_2380255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380255).length < 2 ^ (prefixWord ++ tailWord_2380255).sum := by decide
  have hdescent : baseEnd_2380255 < baseStart_2380255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380268 : List Nat := [2, 2, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_2380268 : Nat := 118140960795 + 2380268 * 2 ^ 59
def prefixEnd_2380268 : Nat := 4983230072969 + 3 ^ 40 * 2380268 * 2
def baseEnd_2380268 : Nat := 814814380344132282802235

theorem tailTrace_2380268 : CollatzResearch.WordTrace tailWord_2380268 prefixEnd_2380268 814814380344132282802235 := by
  unfold tailWord_2380268
  simp only [CollatzResearch.WordTrace]
  refine ⟨43407753070351514127502729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57877004093802018836670305 43407753070351514127502729)
  ·
    refine ⟨32555814802763635595627047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43407753070351514127502729 32555814802763635595627047)
    ·
      refine ⟨48833722204145453393440571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32555814802763635595627047 48833722204145453393440571)
      ·
        refine ⟨73250583306218180090160857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48833722204145453393440571 73250583306218180090160857)
        ·
          refine ⟨54937937479663635067620643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73250583306218180090160857 54937937479663635067620643)
          ·
            refine ⟨82406906219495452601430965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54937937479663635067620643 82406906219495452601430965)
            ·
              refine ⟨7725647458077698681384153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82406906219495452601430965 7725647458077698681384153)
              ·
                refine ⟨5794235593558274011038115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7725647458077698681384153 5794235593558274011038115)
                ·
                  refine ⟨8691353390337411016557173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5794235593558274011038115 8691353390337411016557173)
                  ·
                    refine ⟨814814380344132282802235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8691353390337411016557173 814814380344132282802235)
                    ·
                      rfl

theorem cell22_2380268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_2380268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380268 prefixEnd_2380268 := by exact prefixLift 2380268
  have htrace : WordTrace (prefixWord ++ tailWord_2380268) baseStart_2380268 baseEnd_2380268 := by
    simpa [prefixWord, tailWord_2380268, baseEnd_2380268] using wordTrace_append hprefix tailTrace_2380268
  have hstable : (prefixWord ++ tailWord_2380268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380268).length < 2 ^ (prefixWord ++ tailWord_2380268).sum := by decide
  have hdescent : baseEnd_2380268 < baseStart_2380268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380302 : List Nat := [4, 1, 1, 2, 3, 1, 2, 3, 2, 3]
def baseStart_2380302 : Nat := 118140960795 + 2380302 * 2 ^ 59
def prefixEnd_2380302 : Nat := 4983230072969 + 3 ^ 40 * 2380302 * 2
def baseEnd_2380302 : Nat := 814826019238967527452131

theorem tailTrace_2380302 : CollatzResearch.WordTrace tailWord_2380302 prefixEnd_2380302 814826019238967527452131 := by
  unfold tailWord_2380302
  simp only [CollatzResearch.WordTrace]
  refine ⟨10852093277822481507717895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57877830815053234707828773 10852093277822481507717895)
  ·
    refine ⟨16278139916733722261576843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10852093277822481507717895 16278139916733722261576843)
    ·
      refine ⟨24417209875100583392365265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16278139916733722261576843 24417209875100583392365265)
      ·
        refine ⟨18312907406325437544273949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24417209875100583392365265 18312907406325437544273949)
        ·
          refine ⟨6867340277372039079102731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18312907406325437544273949 6867340277372039079102731)
          ·
            refine ⟨10301010416058058618654097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6867340277372039079102731 10301010416058058618654097)
            ·
              refine ⟨7725757812043543963990573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10301010416058058618654097 7725757812043543963990573)
              ·
                refine ⟨2897159179516328986496465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7725757812043543963990573 2897159179516328986496465)
                ·
                  refine ⟨2172869384637246739872349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2897159179516328986496465 2172869384637246739872349)
                  ·
                    refine ⟨814826019238967527452131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2172869384637246739872349 814826019238967527452131)
                    ·
                      rfl

theorem cell22_2380302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 2, 3, 2, 3].length) (baseStart_2380302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380302 prefixEnd_2380302 := by exact prefixLift 2380302
  have htrace : WordTrace (prefixWord ++ tailWord_2380302) baseStart_2380302 baseEnd_2380302 := by
    simpa [prefixWord, tailWord_2380302, baseEnd_2380302] using wordTrace_append hprefix tailTrace_2380302
  have hstable : (prefixWord ++ tailWord_2380302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380302).length < 2 ^ (prefixWord ++ tailWord_2380302).sum := by decide
  have hdescent : baseEnd_2380302 < baseStart_2380302 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380317 : List Nat := [1, 4, 2, 2, 1, 4, 1, 1, 2, 4]
def baseStart_2380317 : Nat := 118140960795 + 2380317 * 2 ^ 59
def prefixEnd_2380317 : Nat := 4983230072969 + 3 ^ 40 * 2380317 * 2
def baseEnd_2380317 : Nat := 814831154045512488327085

theorem tailTrace_2380317 : CollatzResearch.WordTrace tailWord_2380317 prefixEnd_2380317 814831154045512488327085 := by
  unfold tailWord_2380317
  simp only [CollatzResearch.WordTrace]
  refine ⟨86817293317525509623539205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57878195545017006415692803 86817293317525509623539205)
  ·
    refine ⟨16278242497036033054413601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86817293317525509623539205 16278242497036033054413601)
    ·
      refine ⟨12208681872777024790810201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16278242497036033054413601 12208681872777024790810201)
      ·
        refine ⟨9156511404582768593107651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12208681872777024790810201 9156511404582768593107651)
        ·
          refine ⟨13734767106874152889661477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9156511404582768593107651 13734767106874152889661477)
          ·
            refine ⟨2575268832538903666811527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13734767106874152889661477 2575268832538903666811527)
            ·
              refine ⟨3862903248808355500217291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2575268832538903666811527 3862903248808355500217291)
              ·
                refine ⟨5794354873212533250325937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3862903248808355500217291 5794354873212533250325937)
                ·
                  refine ⟨4345766154909399937744453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5794354873212533250325937 4345766154909399937744453)
                  ·
                    refine ⟨814831154045512488327085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4345766154909399937744453 814831154045512488327085)
                    ·
                      rfl

theorem cell22_2380317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 4, 1, 1, 2, 4].length) (baseStart_2380317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380317 prefixEnd_2380317 := by exact prefixLift 2380317
  have htrace : WordTrace (prefixWord ++ tailWord_2380317) baseStart_2380317 baseEnd_2380317 := by
    simpa [prefixWord, tailWord_2380317, baseEnd_2380317] using wordTrace_append hprefix tailTrace_2380317
  have hstable : (prefixWord ++ tailWord_2380317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380317).length < 2 ^ (prefixWord ++ tailWord_2380317).sum := by decide
  have hdescent : baseEnd_2380317 < baseStart_2380317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380343 : List Nat := [1, 1, 3, 1, 2, 3, 3, 1, 7]
def baseStart_2380343 : Nat := 118140960795 + 2380343 * 2 ^ 59
def prefixEnd_2380343 : Nat := 4983230072969 + 3 ^ 40 * 2380343 * 2
def baseEnd_2380343 : Nat := 271613351458952362392335

theorem tailTrace_2380343 : CollatzResearch.WordTrace tailWord_2380343 prefixEnd_2380343 271613351458952362392335 := by
  unfold tailWord_2380343
  simp only [CollatzResearch.WordTrace]
  refine ⟨86818241615431316063985683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57878827743620877375990455 86818241615431316063985683)
  ·
    refine ⟨130227362423146974095978525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86818241615431316063985683 130227362423146974095978525)
    ·
      refine ⟨48835260908680115285991947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130227362423146974095978525 48835260908680115285991947)
      ·
        refine ⟨73252891363020172928987921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48835260908680115285991947 73252891363020172928987921)
        ·
          refine ⟨54939668522265129696740941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73252891363020172928987921 54939668522265129696740941)
          ·
            refine ⟨20602375695849423636277853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 54939668522265129696740941 20602375695849423636277853)
            ·
              refine ⟨7725890885943533863604195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20602375695849423636277853 7725890885943533863604195)
              ·
                refine ⟨11588836328915300795406293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7725890885943533863604195 11588836328915300795406293)
                ·
                  refine ⟨271613351458952362392335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11588836328915300795406293 271613351458952362392335)
                  ·
                    rfl

theorem cell22_2380343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 1, 7].length) (baseStart_2380343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380343 prefixEnd_2380343 := by exact prefixLift 2380343
  have htrace : WordTrace (prefixWord ++ tailWord_2380343) baseStart_2380343 baseEnd_2380343 := by
    simpa [prefixWord, tailWord_2380343, baseEnd_2380343] using wordTrace_append hprefix tailTrace_2380343
  have hstable : (prefixWord ++ tailWord_2380343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380343).length < 2 ^ (prefixWord ++ tailWord_2380343).sum := by decide
  have hdescent : baseEnd_2380343 < baseStart_2380343 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380403 : List Nat := [1, 1, 1, 2, 2, 1, 1, 3, 5, 5]
def baseStart_2380403 : Nat := 118140960795 + 2380403 * 2 ^ 59
def prefixEnd_2380403 : Nat := 4983230072969 + 3 ^ 40 * 2380403 * 2
def baseEnd_2380403 : Nat := 814860593603036930676821

theorem tailTrace_2380403 : CollatzResearch.WordTrace tailWord_2380403 prefixEnd_2380403 814860593603036930676821 := by
  unfold tailWord_2380403
  simp only [CollatzResearch.WordTrace]
  refine ⟨86820429995213946311169863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57880286663475964207446575 86820429995213946311169863)
  ·
    refine ⟨130230644992820919466754795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86820429995213946311169863 130230644992820919466754795)
    ·
      refine ⟨195345967489231379200132193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130230644992820919466754795 195345967489231379200132193)
      ·
        refine ⟨146509475616923534400099145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195345967489231379200132193 146509475616923534400099145)
        ·
          refine ⟨109882106712692650800074359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146509475616923534400099145 109882106712692650800074359)
          ·
            refine ⟨164823160069038976200111539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109882106712692650800074359 164823160069038976200111539)
            ·
              refine ⟨247234740103558464300167309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 164823160069038976200111539 247234740103558464300167309)
              ·
                refine ⟨92713027538834424112562741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 247234740103558464300167309 92713027538834424112562741)
                ·
                  refine ⟨8691846331765727260552757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 92713027538834424112562741 8691846331765727260552757)
                  ·
                    refine ⟨814860593603036930676821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8691846331765727260552757 814860593603036930676821)
                    ·
                      rfl

theorem cell22_2380403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_2380403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380403 prefixEnd_2380403 := by exact prefixLift 2380403
  have htrace : WordTrace (prefixWord ++ tailWord_2380403) baseStart_2380403 baseEnd_2380403 := by
    simpa [prefixWord, tailWord_2380403, baseEnd_2380403] using wordTrace_append hprefix tailTrace_2380403
  have hstable : (prefixWord ++ tailWord_2380403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380403).length < 2 ^ (prefixWord ++ tailWord_2380403).sum := by decide
  have hdescent : baseEnd_2380403 < baseStart_2380403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380486 : List Nat := [6, 1, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2380486 : Nat := 118140960795 + 2380486 * 2 ^ 59
def prefixEnd_2380486 : Nat := 4983230072969 + 3 ^ 40 * 2380486 * 2
def baseEnd_2380486 : Nat := 814889006199252380851567

theorem tailTrace_2380486 : CollatzResearch.WordTrace tailWord_2380486 prefixEnd_2380486 814889006199252380851567 := by
  unfold tailWord_2380486
  simp only [CollatzResearch.WordTrace]
  refine ⟨2713233039184789108951291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 57882304835942167657627541 2713233039184789108951291)
  ·
    refine ⟨4069849558777183663426937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2713233039184789108951291 4069849558777183663426937)
    ·
      refine ⟨3052387169082887747570203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4069849558777183663426937 3052387169082887747570203)
      ·
        refine ⟨4578580753624331621355305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3052387169082887747570203 4578580753624331621355305)
        ·
          refine ⟨3433935565218248716016479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4578580753624331621355305 3433935565218248716016479)
          ·
            refine ⟨5150903347827373074024719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3433935565218248716016479 5150903347827373074024719)
            ·
              refine ⟨7726355021741059611037079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5150903347827373074024719 7726355021741059611037079)
              ·
                refine ⟨11589532532611589416555619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7726355021741059611037079 11589532532611589416555619)
                ·
                  refine ⟨17384298798917384124833429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11589532532611589416555619 17384298798917384124833429)
                  ·
                    refine ⟨814889006199252380851567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17384298798917384124833429 814889006199252380851567)
                    ·
                      rfl

theorem cell22_2380486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2380486 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380486 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380486 prefixEnd_2380486 := by exact prefixLift 2380486
  have htrace : WordTrace (prefixWord ++ tailWord_2380486) baseStart_2380486 baseEnd_2380486 := by
    simpa [prefixWord, tailWord_2380486, baseEnd_2380486] using wordTrace_append hprefix tailTrace_2380486
  have hstable : (prefixWord ++ tailWord_2380486).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380486).length < 2 ^ (prefixWord ++ tailWord_2380486).sum := by decide
  have hdescent : baseEnd_2380486 < baseStart_2380486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380555 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 3, 5]
def baseStart_2380555 : Nat := 118140960795 + 2380555 * 2 ^ 59
def prefixEnd_2380555 : Nat := 4983230072969 + 3 ^ 40 * 2380555 * 2
def baseEnd_2380555 : Nat := 814912626309359200876355

theorem tailTrace_2380555 : CollatzResearch.WordTrace tailWord_2380555 prefixEnd_2380555 814912626309359200876355 := by
  unfold tailWord_2380555
  simp only [CollatzResearch.WordTrace]
  refine ⟨86825973890663276270703119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57883982593775517513802079 86825973890663276270703119)
  ·
    refine ⟨130238960835994914406054679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86825973890663276270703119 130238960835994914406054679)
    ·
      refine ⟨195358441253992371609082019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130238960835994914406054679 195358441253992371609082019)
      ·
        refine ⟨293037661880988557413623029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195358441253992371609082019 293037661880988557413623029)
        ·
          refine ⟨27472280801342677257527159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 293037661880988557413623029 27472280801342677257527159)
          ·
            refine ⟨41208421202014015886290739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27472280801342677257527159 41208421202014015886290739)
            ·
              refine ⟨61812631803021023829436109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41208421202014015886290739 61812631803021023829436109)
              ·
                refine ⟨23179736926132883936038541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61812631803021023829436109 23179736926132883936038541)
                ·
                  refine ⟨8692401347299831476014453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23179736926132883936038541 8692401347299831476014453)
                  ·
                    refine ⟨814912626309359200876355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8692401347299831476014453 814912626309359200876355)
                    ·
                      rfl

theorem cell22_2380555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_2380555 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380555 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380555 prefixEnd_2380555 := by exact prefixLift 2380555
  have htrace : WordTrace (prefixWord ++ tailWord_2380555) baseStart_2380555 baseEnd_2380555 := by
    simpa [prefixWord, tailWord_2380555, baseEnd_2380555] using wordTrace_append hprefix tailTrace_2380555
  have hstable : (prefixWord ++ tailWord_2380555).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380555).length < 2 ^ (prefixWord ++ tailWord_2380555).sum := by decide
  have hdescent : baseEnd_2380555 < baseStart_2380555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380749 : List Nat := [1, 6, 3, 1, 2, 1, 2, 1, 5]
def baseStart_2380749 : Nat := 118140960795 + 2380749 * 2 ^ 59
def prefixEnd_2380749 : Nat := 4983230072969 + 3 ^ 40 * 2380749 * 2
def baseEnd_2380749 : Nat := 271659678824669120508587

theorem tailTrace_2380749 : CollatzResearch.WordTrace tailWord_2380749 prefixEnd_2380749 271659678824669120508587 := by
  unfold tailWord_2380749
  simp only [CollatzResearch.WordTrace]
  refine ⟨86833049651960447403265301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57888699767973631602176867 86833049651960447403265301)
  ·
    refine ⟨4070299202435645972028061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86833049651960447403265301 4070299202435645972028061)
    ·
      refine ⟨1526362200913367239510523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4070299202435645972028061 1526362200913367239510523)
      ·
        refine ⟨2289543301370050859265785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526362200913367239510523 2289543301370050859265785)
        ·
          refine ⟨1717157476027538144449339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2289543301370050859265785 1717157476027538144449339)
          ·
            refine ⟨2575736214041307216674009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717157476027538144449339 2575736214041307216674009)
            ·
              refine ⟨1931802160530980412505507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2575736214041307216674009 1931802160530980412505507)
              ·
                refine ⟨2897703240796470618758261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1931802160530980412505507 2897703240796470618758261)
                ·
                  refine ⟨271659678824669120508587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2897703240796470618758261 271659678824669120508587)
                  ·
                    rfl

theorem cell22_2380749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_2380749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380749 prefixEnd_2380749 := by exact prefixLift 2380749
  have htrace : WordTrace (prefixWord ++ tailWord_2380749) baseStart_2380749 baseEnd_2380749 := by
    simpa [prefixWord, tailWord_2380749, baseEnd_2380749] using wordTrace_append hprefix tailTrace_2380749
  have hstable : (prefixWord ++ tailWord_2380749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380749).length < 2 ^ (prefixWord ++ tailWord_2380749).sum := by decide
  have hdescent : baseEnd_2380749 < baseStart_2380749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380754 : List Nat := [3, 2, 2, 3, 1, 1, 1, 9]
def baseStart_2380754 : Nat := 118140960795 + 2380754 * 2 ^ 59
def prefixEnd_2380754 : Nat := 4983230072969 + 3 ^ 40 * 2380754 * 2
def baseEnd_2380754 : Nat := 90553416452909890572305

theorem tailTrace_2380754 : CollatzResearch.WordTrace tailWord_2380754 prefixEnd_2380754 90553416452909890572305 := by
  unfold tailWord_2380754
  simp only [CollatzResearch.WordTrace]
  refine ⟨21708308004235583314299329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57888821344628222171464877 21708308004235583314299329)
  ·
    refine ⟨16281231003176687485724497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21708308004235583314299329 16281231003176687485724497)
    ·
      refine ⟨12210923252382515614293373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16281231003176687485724497 12210923252382515614293373)
      ·
        refine ⟨4579096219643443355360015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12210923252382515614293373 4579096219643443355360015)
        ·
          refine ⟨6868644329465165033040023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4579096219643443355360015 6868644329465165033040023)
          ·
            refine ⟨10302966494197747549560035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6868644329465165033040023 10302966494197747549560035)
            ·
              refine ⟨15454449741296621324340053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10302966494197747549560035 15454449741296621324340053)
              ·
                refine ⟨90553416452909890572305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15454449741296621324340053 90553416452909890572305)
                ·
                  rfl

theorem cell22_2380754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_2380754 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380754 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380754 prefixEnd_2380754 := by exact prefixLift 2380754
  have htrace : WordTrace (prefixWord ++ tailWord_2380754) baseStart_2380754 baseEnd_2380754 := by
    simpa [prefixWord, tailWord_2380754, baseEnd_2380754] using wordTrace_append hprefix tailTrace_2380754
  have hstable : (prefixWord ++ tailWord_2380754).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380754).length < 2 ^ (prefixWord ++ tailWord_2380754).sum := by decide
  have hdescent : baseEnd_2380754 < baseStart_2380754 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380769 : List Nat := [1, 2, 3, 1, 2, 1, 1, 3, 5, 3]
def baseStart_2380769 : Nat := 118140960795 + 2380769 * 2 ^ 59
def prefixEnd_2380769 : Nat := 4983230072969 + 3 ^ 40 * 2380769 * 2
def baseEnd_2380769 : Nat := 814985882882733976025699

theorem tailTrace_2380769 : CollatzResearch.WordTrace tailWord_2380769 prefixEnd_2380769 814985882882733976025699 := by
  unfold tailWord_2380769
  simp only [CollatzResearch.WordTrace]
  refine ⟨86833779111887990818993361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57889186074591993879328907 86833779111887990818993361)
  ·
    refine ⟨65125334333915993114245021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86833779111887990818993361 65125334333915993114245021)
    ·
      refine ⟨24422000375218497417841883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65125334333915993114245021 24422000375218497417841883)
      ·
        refine ⟨36633000562827746126762825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24422000375218497417841883 36633000562827746126762825)
        ·
          refine ⟨27474750422120809595072119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36633000562827746126762825 27474750422120809595072119)
          ·
            refine ⟨41212125633181214392608179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27474750422120809595072119 41212125633181214392608179)
            ·
              refine ⟨61818188449771821588912269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41212125633181214392608179 61818188449771821588912269)
              ·
                refine ⟨23181820668664433095842101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61818188449771821588912269 23181820668664433095842101)
                ·
                  refine ⟨2173295687687290602735197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23181820668664433095842101 2173295687687290602735197)
                  ·
                    refine ⟨814985882882733976025699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2173295687687290602735197 814985882882733976025699)
                    ·
                      rfl

theorem cell22_2380769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_2380769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380769 prefixEnd_2380769 := by exact prefixLift 2380769
  have htrace : WordTrace (prefixWord ++ tailWord_2380769) baseStart_2380769 baseEnd_2380769 := by
    simpa [prefixWord, tailWord_2380769, baseEnd_2380769] using wordTrace_append hprefix tailTrace_2380769
  have hstable : (prefixWord ++ tailWord_2380769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380769).length < 2 ^ (prefixWord ++ tailWord_2380769).sum := by decide
  have hdescent : baseEnd_2380769 < baseStart_2380769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380773 : List Nat := [1, 3, 1, 6, 1, 1, 2, 1, 2, 4]
def baseStart_2380773 : Nat := 118140960795 + 2380773 * 2 ^ 59
def prefixEnd_2380773 : Nat := 4983230072969 + 3 ^ 40 * 2380773 * 2
def baseEnd_2380773 : Nat := 814987252164479298925687

theorem tailTrace_2380773 : CollatzResearch.WordTrace tailWord_2380773 prefixEnd_2380773 814987252164479298925687 := by
  unfold tailWord_2380773
  simp only [CollatzResearch.WordTrace]
  refine ⟨86833925003873499502138973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57889283335915666334759315 86833925003873499502138973)
  ·
    refine ⟨32562721876452562313302115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86833925003873499502138973 32562721876452562313302115)
    ·
      refine ⟨48844082814678843469953173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32562721876452562313302115 48844082814678843469953173)
      ·
        refine ⟨2289566381938070787654055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48844082814678843469953173 2289566381938070787654055)
        ·
          refine ⟨3434349572907106181481083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2289566381938070787654055 3434349572907106181481083)
          ·
            refine ⟨5151524359360659272221625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434349572907106181481083 5151524359360659272221625)
            ·
              refine ⟨3863643269520494454166219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5151524359360659272221625 3863643269520494454166219)
              ·
                refine ⟨5795464904280741681249329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3863643269520494454166219 5795464904280741681249329)
                ·
                  refine ⟨4346598678210556260936997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5795464904280741681249329 4346598678210556260936997)
                  ·
                    refine ⟨814987252164479298925687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4346598678210556260936997 814987252164479298925687)
                    ·
                      rfl

theorem cell22_2380773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 2, 1, 2, 4].length) (baseStart_2380773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380773 prefixEnd_2380773 := by exact prefixLift 2380773
  have htrace : WordTrace (prefixWord ++ tailWord_2380773) baseStart_2380773 baseEnd_2380773 := by
    simpa [prefixWord, tailWord_2380773, baseEnd_2380773] using wordTrace_append hprefix tailTrace_2380773
  have hstable : (prefixWord ++ tailWord_2380773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380773).length < 2 ^ (prefixWord ++ tailWord_2380773).sum := by decide
  have hdescent : baseEnd_2380773 < baseStart_2380773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380788 : List Nat := [2, 6, 2, 1, 11]
def baseStart_2380788 : Nat := 118140960795 + 2380788 * 2 ^ 59
def prefixEnd_2380788 : Nat := 4983230072969 + 3 ^ 40 * 2380788 * 2
def baseEnd_2380788 : Nat := 3353878135683227406587

theorem tailTrace_2380788 : CollatzResearch.WordTrace tailWord_2380788 prefixEnd_2380788 3353878135683227406587 := by
  unfold tailWord_2380788
  simp only [CollatzResearch.WordTrace]
  refine ⟨43417236049409578531967509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57889648065879438042623345 43417236049409578531967509)
  ·
    refine ⟨2035182939816073993685977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43417236049409578531967509 2035182939816073993685977)
    ·
      refine ⟨1526387204862055495264483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2035182939816073993685977 1526387204862055495264483)
      ·
        refine ⟨2289580807293083242896725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526387204862055495264483 2289580807293083242896725)
        ·
          refine ⟨3353878135683227406587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 2289580807293083242896725 3353878135683227406587)
          ·
            rfl

theorem cell22_2380788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 11].length) (baseStart_2380788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380788 prefixEnd_2380788 := by exact prefixLift 2380788
  have htrace : WordTrace (prefixWord ++ tailWord_2380788) baseStart_2380788 baseEnd_2380788 := by
    simpa [prefixWord, tailWord_2380788, baseEnd_2380788] using wordTrace_append hprefix tailTrace_2380788
  have hstable : (prefixWord ++ tailWord_2380788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380788).length < 2 ^ (prefixWord ++ tailWord_2380788).sum := by decide
  have hdescent : baseEnd_2380788 < baseStart_2380788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380814 : List Nat := [4, 1, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_2380814 : Nat := 118140960795 + 2380814 * 2 ^ 59
def prefixEnd_2380814 : Nat := 4983230072969 + 3 ^ 40 * 2380814 * 2
def baseEnd_2380814 : Nat := 815001287302368858650561

theorem tailTrace_2380814 : CollatzResearch.WordTrace tailWord_2380814 prefixEnd_2380814 815001287302368858650561 := by
  unfold tailWord_2380814
  simp only [CollatzResearch.WordTrace]
  refine ⟨10854427549590620438047687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57890280264483309002920997 10854427549590620438047687)
  ·
    refine ⟨16281641324385930657071531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10854427549590620438047687 16281641324385930657071531)
    ·
      refine ⟨24422461986578895985607297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16281641324385930657071531 24422461986578895985607297)
      ·
        refine ⟨18316846489934171989205473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24422461986578895985607297 18316846489934171989205473)
        ·
          refine ⟨13737634867450628991904105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18316846489934171989205473 13737634867450628991904105)
          ·
            refine ⟨10303226150587971743928079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13737634867450628991904105 10303226150587971743928079)
            ·
              refine ⟨15454839225881957615892119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10303226150587971743928079 15454839225881957615892119)
              ·
                refine ⟨23182258838822936423838179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15454839225881957615892119 23182258838822936423838179)
                ·
                  refine ⟨34773388258234404635757269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23182258838822936423838179 34773388258234404635757269)
                  ·
                    refine ⟨815001287302368858650561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34773388258234404635757269 815001287302368858650561)
                    ·
                      rfl

theorem cell22_2380814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_2380814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380814 prefixEnd_2380814 := by exact prefixLift 2380814
  have htrace : WordTrace (prefixWord ++ tailWord_2380814) baseStart_2380814 baseEnd_2380814 := by
    simpa [prefixWord, tailWord_2380814, baseEnd_2380814] using wordTrace_append hprefix tailTrace_2380814
  have hstable : (prefixWord ++ tailWord_2380814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380814).length < 2 ^ (prefixWord ++ tailWord_2380814).sum := by decide
  have hdescent : baseEnd_2380814 < baseStart_2380814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380861 : List Nat := [1, 4, 1, 3, 1, 3, 2, 1, 6]
def baseStart_2380861 : Nat := 118140960795 + 2380861 * 2 ^ 59
def prefixEnd_2380861 : Nat := 4983230072969 + 3 ^ 40 * 2380861 * 2
def baseEnd_2380861 : Nat := 271672458787625467575139

theorem tailTrace_2380861 : CollatzResearch.WordTrace tailWord_2380861 prefixEnd_2380861 271672458787625467575139 := by
  unfold tailWord_2380861
  simp only [CollatzResearch.WordTrace]
  refine ⟨86837134627554690531342437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57891423085036460354228291 86837134627554690531342437)
  ·
    refine ⟨16281962742666504474626707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86837134627554690531342437 16281962742666504474626707)
    ·
      refine ⟨24422944113999756711940061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16281962742666504474626707 24422944113999756711940061)
      ·
        refine ⟨9158604042749908766977523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24422944113999756711940061 9158604042749908766977523)
        ·
          refine ⟨13737906064124863150466285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9158604042749908766977523 13737906064124863150466285)
          ·
            refine ⟨5151714774046823681424857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13737906064124863150466285 5151714774046823681424857)
            ·
              refine ⟨3863786080535117761068643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5151714774046823681424857 3863786080535117761068643)
              ·
                refine ⟨5795679120802676641602965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3863786080535117761068643 5795679120802676641602965)
                ·
                  refine ⟨271672458787625467575139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5795679120802676641602965 271672458787625467575139)
                  ·
                    rfl

theorem cell22_2380861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_2380861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380861 prefixEnd_2380861 := by exact prefixLift 2380861
  have htrace : WordTrace (prefixWord ++ tailWord_2380861) baseStart_2380861 baseEnd_2380861 := by
    simpa [prefixWord, tailWord_2380861, baseEnd_2380861] using wordTrace_append hprefix tailTrace_2380861
  have hstable : (prefixWord ++ tailWord_2380861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380861).length < 2 ^ (prefixWord ++ tailWord_2380861).sum := by decide
  have hdescent : baseEnd_2380861 < baseStart_2380861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380874 : List Nat := [3, 1, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_2380874 : Nat := 118140960795 + 2380874 * 2 ^ 59
def prefixEnd_2380874 : Nat := 4983230072969 + 3 ^ 40 * 2380874 * 2
def baseEnd_2380874 : Nat := 815021826528548702150377

theorem tailTrace_2380874 : CollatzResearch.WordTrace tailWord_2380874 prefixEnd_2380874 815021826528548702150377 := by
  unfold tailWord_2380874
  simp only [CollatzResearch.WordTrace]
  refine ⟨21709402194126898437891419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57891739184338395834377117 21709402194126898437891419)
  ·
    refine ⟨32564103291190347656837129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21709402194126898437891419 32564103291190347656837129)
    ·
      refine ⟨24423077468392760742627847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32564103291190347656837129 24423077468392760742627847)
      ·
        refine ⟨36634616202589141113941771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24423077468392760742627847 36634616202589141113941771)
        ·
          refine ⟨54951924303883711670912657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36634616202589141113941771 54951924303883711670912657)
          ·
            refine ⟨41213943227912783753184493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54951924303883711670912657 41213943227912783753184493)
            ·
              refine ⟨15455228710467293907444185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41213943227912783753184493 15455228710467293907444185)
              ·
                refine ⟨11591421532850470430583139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15455228710467293907444185 11591421532850470430583139)
                ·
                  refine ⟨17387132299275705645874709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11591421532850470430583139 17387132299275705645874709)
                  ·
                    refine ⟨815021826528548702150377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17387132299275705645874709 815021826528548702150377)
                    ·
                      rfl

theorem cell22_2380874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_2380874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380874 prefixEnd_2380874 := by exact prefixLift 2380874
  have htrace : WordTrace (prefixWord ++ tailWord_2380874) baseStart_2380874 baseEnd_2380874 := by
    simpa [prefixWord, tailWord_2380874, baseEnd_2380874] using wordTrace_append hprefix tailTrace_2380874
  have hstable : (prefixWord ++ tailWord_2380874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380874).length < 2 ^ (prefixWord ++ tailWord_2380874).sum := by decide
  have hdescent : baseEnd_2380874 < baseStart_2380874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380906 : List Nat := [3, 1, 3, 2, 2, 3, 8]
def baseStart_2380906 : Nat := 118140960795 + 2380906 * 2 ^ 59
def prefixEnd_2380906 : Nat := 4983230072969 + 3 ^ 40 * 2380906 * 2
def baseEnd_2380906 : Nat := 30186399288241158716677

theorem tailTrace_2380906 : CollatzResearch.WordTrace tailWord_2380906 prefixEnd_2380906 30186399288241158716677 := by
  unfold tailWord_2380906
  simp only [CollatzResearch.WordTrace]
  refine ⟨21709693978097915804182643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57892517274927775477820381 21709693978097915804182643)
  ·
    refine ⟨32564540967146873706273965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21709693978097915804182643 32564540967146873706273965)
    ·
      refine ⟨12211702862680077639852737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32564540967146873706273965 12211702862680077639852737)
      ·
        refine ⟨9158777147010058229889553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12211702862680077639852737 9158777147010058229889553)
        ·
          refine ⟨6869082860257543672417165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9158777147010058229889553 6869082860257543672417165)
          ·
            refine ⟨2575906072596578877156437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6869082860257543672417165 2575906072596578877156437)
            ·
              refine ⟨30186399288241158716677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2575906072596578877156437 30186399288241158716677)
              ·
                rfl

theorem cell22_2380906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 8].length) (baseStart_2380906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380906 prefixEnd_2380906 := by exact prefixLift 2380906
  have htrace : WordTrace (prefixWord ++ tailWord_2380906) baseStart_2380906 baseEnd_2380906 := by
    simpa [prefixWord, tailWord_2380906, baseEnd_2380906] using wordTrace_append hprefix tailTrace_2380906
  have hstable : (prefixWord ++ tailWord_2380906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380906).length < 2 ^ (prefixWord ++ tailWord_2380906).sum := by decide
  have hdescent : baseEnd_2380906 < baseStart_2380906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380919 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 2, 6]
def baseStart_2380919 : Nat := 118140960795 + 2380919 * 2 ^ 59
def prefixEnd_2380919 : Nat := 4983230072969 + 3 ^ 40 * 2380919 * 2
def baseEnd_2380919 : Nat := 815037230948183584775239

theorem tailTrace_2380919 : CollatzResearch.WordTrace tailWord_2380919 prefixEnd_2380919 815037230948183584775239 := by
  unfold tailWord_2380919
  simp only [CollatzResearch.WordTrace]
  refine ⟨86839250061344566436953811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57892833374229710957969207 86839250061344566436953811)
  ·
    refine ⟨130258875092016849655430717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86839250061344566436953811 130258875092016849655430717)
    ·
      refine ⟨48847078159506318620786519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130258875092016849655430717 48847078159506318620786519)
      ·
        refine ⟨73270617239259477931179779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48847078159506318620786519 73270617239259477931179779)
        ·
          refine ⟨109905925858889216896769669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73270617239259477931179779 109905925858889216896769669)
          ·
            refine ⟨20607361098541728168144313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109905925858889216896769669 20607361098541728168144313)
            ·
              refine ⟨15455520823906296126108235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20607361098541728168144313 15455520823906296126108235)
              ·
                refine ⟨23183281235859444189162353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15455520823906296126108235 23183281235859444189162353)
                ·
                  refine ⟨17387460926894583141871765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23183281235859444189162353 17387460926894583141871765)
                  ·
                    refine ⟨815037230948183584775239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17387460926894583141871765 815037230948183584775239)
                    ·
                      rfl

theorem cell22_2380919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_2380919 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380919 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380919 prefixEnd_2380919 := by exact prefixLift 2380919
  have htrace : WordTrace (prefixWord ++ tailWord_2380919) baseStart_2380919 baseEnd_2380919 := by
    simpa [prefixWord, tailWord_2380919, baseEnd_2380919] using wordTrace_append hprefix tailTrace_2380919
  have hstable : (prefixWord ++ tailWord_2380919).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380919).length < 2 ^ (prefixWord ++ tailWord_2380919).sum := by decide
  have hdescent : baseEnd_2380919 < baseStart_2380919 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2380949 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_2380949 : Nat := 118140960795 + 2380949 * 2 ^ 59
def prefixEnd_2380949 : Nat := 4983230072969 + 3 ^ 40 * 2380949 * 2
def baseEnd_2380949 : Nat := 815047500561273506525147

theorem tailTrace_2380949 : CollatzResearch.WordTrace tailWord_2380949 prefixEnd_2380949 815047500561273506525147 := by
  unfold tailWord_2380949
  simp only [CollatzResearch.WordTrace]
  refine ⟨86840344251235881560545901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57893562834157254373697267 86840344251235881560545901)
  ·
    refine ⟨32565129094213455585204713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86840344251235881560545901 32565129094213455585204713)
    ·
      refine ⟨24423846820660091688903535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32565129094213455585204713 24423846820660091688903535)
      ·
        refine ⟨36635770230990137533355303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24423846820660091688903535 36635770230990137533355303)
        ·
          refine ⟨54953655346485206300032955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36635770230990137533355303 54953655346485206300032955)
          ·
            refine ⟨82430483019727809450049433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54953655346485206300032955 82430483019727809450049433)
            ·
              refine ⟨61822862264795857087537075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82430483019727809450049433 61822862264795857087537075)
              ·
                refine ⟨92734293397193785631305613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61822862264795857087537075 92734293397193785631305613)
                ·
                  refine ⟨34775360023947669611739605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92734293397193785631305613 34775360023947669611739605)
                  ·
                    refine ⟨815047500561273506525147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34775360023947669611739605 815047500561273506525147)
                    ·
                      rfl

theorem cell22_2380949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_2380949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2380949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2380949 prefixEnd_2380949 := by exact prefixLift 2380949
  have htrace : WordTrace (prefixWord ++ tailWord_2380949) baseStart_2380949 baseEnd_2380949 := by
    simpa [prefixWord, tailWord_2380949, baseEnd_2380949] using wordTrace_append hprefix tailTrace_2380949
  have hstable : (prefixWord ++ tailWord_2380949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2380949).length < 2 ^ (prefixWord ++ tailWord_2380949).sum := by decide
  have hdescent : baseEnd_2380949 < baseStart_2380949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2380949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381011 : List Nat := [1, 1, 1, 2, 1, 1, 1, 5, 6, 3]
def baseStart_2381011 : Nat := 118140960795 + 2381011 * 2 ^ 59
def prefixEnd_2381011 : Nat := 4983230072969 + 3 ^ 40 * 2381011 * 2
def baseEnd_2381011 : Nat := 815068724428326011474957

theorem tailTrace_2381011 : CollatzResearch.WordTrace tailWord_2381011 prefixEnd_2381011 815068724428326011474957 := by
  unfold tailWord_2381011
  simp only [CollatzResearch.WordTrace]
  refine ⟨86842605577011266149302887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57895070384674177432868591 86842605577011266149302887)
  ·
    refine ⟨130263908365516899223954331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86842605577011266149302887 130263908365516899223954331)
    ·
      refine ⟨195395862548275348835931497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130263908365516899223954331 195395862548275348835931497)
      ·
        refine ⟨146546896911206511626948623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195395862548275348835931497 146546896911206511626948623)
        ·
          refine ⟨219820345366809767440422935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146546896911206511626948623 219820345366809767440422935)
          ·
            refine ⟨329730518050214651160634403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 219820345366809767440422935 329730518050214651160634403)
            ·
              refine ⟨494595777075321976740951605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 329730518050214651160634403 494595777075321976740951605)
              ·
                refine ⟨46368354100811435319464213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 494595777075321976740951605 46368354100811435319464213)
                ·
                  refine ⟨2173516598475536030599885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46368354100811435319464213 2173516598475536030599885)
                  ·
                    refine ⟨815068724428326011474957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2173516598475536030599885 815068724428326011474957)
                    ·
                      rfl

theorem cell22_2381011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 5, 6, 3].length) (baseStart_2381011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381011 prefixEnd_2381011 := by exact prefixLift 2381011
  have htrace : WordTrace (prefixWord ++ tailWord_2381011) baseStart_2381011 baseEnd_2381011 := by
    simpa [prefixWord, tailWord_2381011, baseEnd_2381011] using wordTrace_append hprefix tailTrace_2381011
  have hstable : (prefixWord ++ tailWord_2381011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381011).length < 2 ^ (prefixWord ++ tailWord_2381011).sum := by decide
  have hdescent : baseEnd_2381011 < baseStart_2381011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381193 : List Nat := [1, 2, 1, 1, 7, 1, 9]
def baseStart_2381193 : Nat := 118140960795 + 2381193 * 2 ^ 59
def prefixEnd_2381193 : Nat := 4983230072969 + 3 ^ 40 * 2381193 * 2
def baseEnd_2381193 : Nat := 30190038027694007534237

theorem tailTrace_2381193 : CollatzResearch.WordTrace tailWord_2381193 prefixEnd_2381193 30190038027694007534237 := by
  unfold tailWord_2381193
  simp only [CollatzResearch.WordTrace]
  refine ⟨86849243662351911232428233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57899495774901274154952155 86849243662351911232428233)
  ·
    refine ⟨65136932746763933424321175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86849243662351911232428233 65136932746763933424321175)
    ·
      refine ⟨97705399120145900136481763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65136932746763933424321175 97705399120145900136481763)
      ·
        refine ⟨146558098680218850204722645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97705399120145900136481763 146558098680218850204722645)
        ·
          refine ⟨3434955437817629301673187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 146558098680218850204722645 3434955437817629301673187)
          ·
            refine ⟨5152433156726443952509781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3434955437817629301673187 5152433156726443952509781)
            ·
              refine ⟨30190038027694007534237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5152433156726443952509781 30190038027694007534237)
              ·
                rfl

theorem cell22_2381193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 9].length) (baseStart_2381193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381193 prefixEnd_2381193 := by exact prefixLift 2381193
  have htrace : WordTrace (prefixWord ++ tailWord_2381193) baseStart_2381193 baseEnd_2381193 := by
    simpa [prefixWord, tailWord_2381193, baseEnd_2381193] using wordTrace_append hprefix tailTrace_2381193
  have hstable : (prefixWord ++ tailWord_2381193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381193).length < 2 ^ (prefixWord ++ tailWord_2381193).sum := by decide
  have hdescent : baseEnd_2381193 < baseStart_2381193 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381214 : List Nat := [4, 3, 1, 2, 2, 2, 1, 1, 1, 5]
def baseStart_2381214 : Nat := 118140960795 + 2381214 * 2 ^ 59
def prefixEnd_2381214 : Nat := 4983230072969 + 3 ^ 40 * 2381214 * 2
def baseEnd_2381214 : Nat := 815138215476901148649335

theorem tailTrace_2381214 : CollatzResearch.WordTrace tailWord_2381214 prefixEnd_2381214 815138215476901148649335 := by
  unfold tailWord_2381214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856251199409478977367837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57900006396850554545961797 10856251199409478977367837)
  ·
    refine ⟨4071094199778554616512939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10856251199409478977367837 4071094199778554616512939)
    ·
      refine ⟨6106641299667831924769409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4071094199778554616512939 6106641299667831924769409)
      ·
        refine ⟨4579980974750873943577057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6106641299667831924769409 4579980974750873943577057)
        ·
          refine ⟨3434985731063155457682793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4579980974750873943577057 3434985731063155457682793)
          ·
            refine ⟨2576239298297366593262095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3434985731063155457682793 2576239298297366593262095)
            ·
              refine ⟨3864358947446049889893143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576239298297366593262095 3864358947446049889893143)
              ·
                refine ⟨5796538421169074834839715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3864358947446049889893143 5796538421169074834839715)
                ·
                  refine ⟨8694807631753612252259573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5796538421169074834839715 8694807631753612252259573)
                  ·
                    refine ⟨815138215476901148649335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8694807631753612252259573 815138215476901148649335)
                    ·
                      rfl

theorem cell22_2381214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_2381214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381214 prefixEnd_2381214 := by exact prefixLift 2381214
  have htrace : WordTrace (prefixWord ++ tailWord_2381214) baseStart_2381214 baseEnd_2381214 := by
    simpa [prefixWord, tailWord_2381214, baseEnd_2381214] using wordTrace_append hprefix tailTrace_2381214
  have hstable : (prefixWord ++ tailWord_2381214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381214).length < 2 ^ (prefixWord ++ tailWord_2381214).sum := by decide
  have hdescent : baseEnd_2381214 < baseStart_2381214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381250 : List Nat := [3, 5, 2, 1, 1, 1, 3, 2, 4]
def baseStart_2381250 : Nat := 118140960795 + 2381250 * 2 ^ 59
def prefixEnd_2381250 : Nat := 4983230072969 + 3 ^ 40 * 2381250 * 2
def baseEnd_2381250 : Nat := 271716846337536351583075

theorem tailTrace_2381250 : CollatzResearch.WordTrace tailWord_2381250 prefixEnd_2381250 271716846337536351583075 := by
  unfold tailWord_2381250
  simp only [CollatzResearch.WordTrace]
  refine ⟨21712830655786352491813301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57900881748763606644835469 21712830655786352491813301)
  ·
    refine ⟨2035577873979970546107497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21712830655786352491813301 2035577873979970546107497)
    ·
      refine ⟨1526683405484977909580623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2035577873979970546107497 1526683405484977909580623)
      ·
        refine ⟨2290025108227466864370935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1526683405484977909580623 2290025108227466864370935)
        ·
          refine ⟨3435037662341200296556403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290025108227466864370935 3435037662341200296556403)
          ·
            refine ⟨5152556493511800444834605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435037662341200296556403 5152556493511800444834605)
            ·
              refine ⟨1932208685066925166812977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5152556493511800444834605 1932208685066925166812977)
              ·
                refine ⟨1449156513800193875109733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932208685066925166812977 1449156513800193875109733)
                ·
                  refine ⟨271716846337536351583075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1449156513800193875109733 271716846337536351583075)
                  ·
                    rfl

theorem cell22_2381250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_2381250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381250 prefixEnd_2381250 := by exact prefixLift 2381250
  have htrace : WordTrace (prefixWord ++ tailWord_2381250) baseStart_2381250 baseEnd_2381250 := by
    simpa [prefixWord, tailWord_2381250, baseEnd_2381250] using wordTrace_append hprefix tailTrace_2381250
  have hstable : (prefixWord ++ tailWord_2381250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381250).length < 2 ^ (prefixWord ++ tailWord_2381250).sum := by decide
  have hdescent : baseEnd_2381250 < baseStart_2381250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381310 : List Nat := [4, 2, 2, 3, 1, 2, 2, 2, 1, 3]
def baseStart_2381310 : Nat := 118140960795 + 2381310 * 2 ^ 59
def prefixEnd_2381310 : Nat := 4983230072969 + 3 ^ 40 * 2381310 * 2
def baseEnd_2381310 : Nat := 815171078238788898249041

theorem tailTrace_2381310 : CollatzResearch.WordTrace tailWord_2381310 prefixEnd_2381310 815171078238788898249041 := by
  unfold tailWord_2381310
  simp only [CollatzResearch.WordTrace]
  refine ⟨10856688875366005026804673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57902340668618693476291589 10856688875366005026804673)
  ·
    refine ⟨8142516656524503770103505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10856688875366005026804673 8142516656524503770103505)
    ·
      refine ⟨6106887492393377827577629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8142516656524503770103505 6106887492393377827577629)
      ·
        refine ⟨2290082809647516685341611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6106887492393377827577629 2290082809647516685341611)
        ·
          refine ⟨3435124214471275028012417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290082809647516685341611 3435124214471275028012417)
          ·
            refine ⟨2576343160853456271009313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3435124214471275028012417 2576343160853456271009313)
            ·
              refine ⟨1932257370640092203256985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576343160853456271009313 1932257370640092203256985)
              ·
                refine ⟨1449193027980069152442739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932257370640092203256985 1449193027980069152442739)
                ·
                  refine ⟨2173789541970103728664109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449193027980069152442739 2173789541970103728664109)
                  ·
                    refine ⟨815171078238788898249041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2173789541970103728664109 815171078238788898249041)
                    ·
                      rfl

theorem cell22_2381310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 2, 2, 1, 3].length) (baseStart_2381310 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381310 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381310 prefixEnd_2381310 := by exact prefixLift 2381310
  have htrace : WordTrace (prefixWord ++ tailWord_2381310) baseStart_2381310 baseEnd_2381310 := by
    simpa [prefixWord, tailWord_2381310, baseEnd_2381310] using wordTrace_append hprefix tailTrace_2381310
  have hstable : (prefixWord ++ tailWord_2381310).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381310).length < 2 ^ (prefixWord ++ tailWord_2381310).sum := by decide
  have hdescent : baseEnd_2381310 < baseStart_2381310 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381360 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 7, 3]
def baseStart_2381360 : Nat := 118140960795 + 2381360 * 2 ^ 59
def prefixEnd_2381360 : Nat := 4983230072969 + 3 ^ 40 * 2381360 * 2
def baseEnd_2381360 : Nat := 815188194260605434498887

theorem tailTrace_2381360 : CollatzResearch.WordTrace tailWord_2381360 prefixEnd_2381360 815188194260605434498887 := by
  unfold tailWord_2381360
  simp only [CollatzResearch.WordTrace]
  refine ⟨43427667326373449376878767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57903556435164599169171689 43427667326373449376878767)
  ·
    refine ⟨65141500989560174065318151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43427667326373449376878767 65141500989560174065318151)
    ·
      refine ⟨97712251484340261097977227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65141500989560174065318151 97712251484340261097977227)
      ·
        refine ⟨146568377226510391646965841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97712251484340261097977227 146568377226510391646965841)
        ·
          refine ⟨109926282919882793735224381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146568377226510391646965841 109926282919882793735224381)
          ·
            refine ⟨41222356094956047650709143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 109926282919882793735224381 41222356094956047650709143)
            ·
              refine ⟨61833534142434071476063715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41222356094956047650709143 61833534142434071476063715)
              ·
                refine ⟨92750301213651107214095573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61833534142434071476063715 92750301213651107214095573)
                ·
                  refine ⟨2173835184694947825330365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 92750301213651107214095573 2173835184694947825330365)
                  ·
                    refine ⟨815188194260605434498887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2173835184694947825330365 815188194260605434498887)
                    ·
                      rfl

theorem cell22_2381360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 7, 3].length) (baseStart_2381360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381360 prefixEnd_2381360 := by exact prefixLift 2381360
  have htrace : WordTrace (prefixWord ++ tailWord_2381360) baseStart_2381360 baseEnd_2381360 := by
    simpa [prefixWord, tailWord_2381360, baseEnd_2381360] using wordTrace_append hprefix tailTrace_2381360
  have hstable : (prefixWord ++ tailWord_2381360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381360).length < 2 ^ (prefixWord ++ tailWord_2381360).sum := by decide
  have hdescent : baseEnd_2381360 < baseStart_2381360 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381411 : List Nat := [1, 1, 1, 5, 1, 5, 1, 3, 1, 3]
def baseStart_2381411 : Nat := 118140960795 + 2381411 * 2 ^ 59
def prefixEnd_2381411 : Nat := 4983230072969 + 3 ^ 40 * 2381411 * 2
def baseEnd_2381411 : Nat := 815205652602858301473731

theorem tailTrace_2381411 : CollatzResearch.WordTrace tailWord_2381411 prefixEnd_2381411 815205652602858301473731 := by
  unfold tailWord_2381411
  simp only [CollatzResearch.WordTrace]
  refine ⟨86857194775562134463864087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57904796517041422975909391 86857194775562134463864087)
  ·
    refine ⟨130285792163343201695796131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86857194775562134463864087 130285792163343201695796131)
    ·
      refine ⟨195428688245014802543694197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130285792163343201695796131 195428688245014802543694197)
      ·
        refine ⟨18321439522970137738471331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 195428688245014802543694197 18321439522970137738471331)
        ·
          refine ⟨27482159284455206607706997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18321439522970137738471331 27482159284455206607706997)
          ·
            refine ⟨2576452432917675619472531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 27482159284455206607706997 2576452432917675619472531)
            ·
              refine ⟨3864678649376513429208797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576452432917675619472531 3864678649376513429208797)
              ·
                refine ⟨1449254493516192535953299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3864678649376513429208797 1449254493516192535953299)
                ·
                  refine ⟨2173881740274288803929949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449254493516192535953299 2173881740274288803929949)
                  ·
                    refine ⟨815205652602858301473731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2173881740274288803929949 815205652602858301473731)
                    ·
                      rfl

theorem cell22_2381411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 5, 1, 3, 1, 3].length) (baseStart_2381411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381411 prefixEnd_2381411 := by exact prefixLift 2381411
  have htrace : WordTrace (prefixWord ++ tailWord_2381411) baseStart_2381411 baseEnd_2381411 := by
    simpa [prefixWord, tailWord_2381411, baseEnd_2381411] using wordTrace_append hprefix tailTrace_2381411
  have hstable : (prefixWord ++ tailWord_2381411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381411).length < 2 ^ (prefixWord ++ tailWord_2381411).sum := by decide
  have hdescent : baseEnd_2381411 < baseStart_2381411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381420 : List Nat := [2, 2, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_2381420 : Nat := 118140960795 + 2381420 * 2 ^ 59
def prefixEnd_2381420 : Nat := 4983230072969 + 3 ^ 40 * 2381420 * 2
def baseEnd_2381420 : Nat := 815208733486785277998703

theorem tailTrace_2381420 : CollatzResearch.WordTrace tailWord_2381420 prefixEnd_2381420 815208733486785277998703 := by
  unfold tailWord_2381420
  simp only [CollatzResearch.WordTrace]
  refine ⟨43428761516264764500470857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57905015355019686000627809 43428761516264764500470857)
  ·
    refine ⟨32571571137198573375353143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43428761516264764500470857 32571571137198573375353143)
    ·
      refine ⟨48857356705797860063029715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32571571137198573375353143 48857356705797860063029715)
      ·
        refine ⟨73286035058696790094544573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48857356705797860063029715 73286035058696790094544573)
        ·
          refine ⟨27482263147011296285454215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73286035058696790094544573 27482263147011296285454215)
          ·
            refine ⟨41223394720516944428181323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27482263147011296285454215 41223394720516944428181323)
            ·
              refine ⟨61835092080775416642271985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41223394720516944428181323 61835092080775416642271985)
              ·
                refine ⟨46376319060581562481703989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61835092080775416642271985 46376319060581562481703989)
                ·
                  refine ⟨4347779911929521482659749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46376319060581562481703989 4347779911929521482659749)
                  ·
                    refine ⟨815208733486785277998703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4347779911929521482659749 815208733486785277998703)
                    ·
                      rfl

theorem cell22_2381420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_2381420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381420 prefixEnd_2381420 := by exact prefixLift 2381420
  have htrace : WordTrace (prefixWord ++ tailWord_2381420) baseStart_2381420 baseEnd_2381420 := by
    simpa [prefixWord, tailWord_2381420, baseEnd_2381420] using wordTrace_append hprefix tailTrace_2381420
  have hstable : (prefixWord ++ tailWord_2381420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381420).length < 2 ^ (prefixWord ++ tailWord_2381420).sum := by decide
  have hdescent : baseEnd_2381420 < baseStart_2381420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381454 : List Nat := [4, 1, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_2381454 : Nat := 118140960795 + 2381454 * 2 ^ 59
def prefixEnd_2381454 : Nat := 4983230072969 + 3 ^ 40 * 2381454 * 2
def baseEnd_2381454 : Nat := 815220372381620522648599

theorem tailTrace_2381454 : CollatzResearch.WordTrace tailWord_2381454 prefixEnd_2381454 815220372381620522648599 := by
  unfold tailWord_2381454
  simp only [CollatzResearch.WordTrace]
  refine ⟨10857345389300794100959927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57905842076270901871786277 10857345389300794100959927)
  ·
    refine ⟨16286018083951191151439891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10857345389300794100959927 16286018083951191151439891)
    ·
      refine ⟨24429027125926786727159837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16286018083951191151439891 24429027125926786727159837)
      ·
        refine ⟨9160885172222545022684939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24429027125926786727159837 9160885172222545022684939)
        ·
          refine ⟨13741327758333817534027409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9160885172222545022684939 13741327758333817534027409)
          ·
            refine ⟨10305995818750363150520557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13741327758333817534027409 10305995818750363150520557)
            ·
              refine ⟨3864748432031386181445209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10305995818750363150520557 3864748432031386181445209)
              ·
                refine ⟨2898561324023539636083907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3864748432031386181445209 2898561324023539636083907)
                ·
                  refine ⟨4347841986035309454125861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898561324023539636083907 4347841986035309454125861)
                  ·
                    refine ⟨815220372381620522648599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4347841986035309454125861 815220372381620522648599)
                    ·
                      rfl

theorem cell22_2381454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_2381454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381454 prefixEnd_2381454 := by exact prefixLift 2381454
  have htrace : WordTrace (prefixWord ++ tailWord_2381454) baseStart_2381454 baseEnd_2381454 := by
    simpa [prefixWord, tailWord_2381454, baseEnd_2381454] using wordTrace_append hprefix tailTrace_2381454
  have hstable : (prefixWord ++ tailWord_2381454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381454).length < 2 ^ (prefixWord ++ tailWord_2381454).sum := by decide
  have hdescent : baseEnd_2381454 < baseStart_2381454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381514 : List Nat := [3, 1, 2, 1, 5, 1, 3, 6]
def baseStart_2381514 : Nat := 118140960795 + 2381514 * 2 ^ 59
def prefixEnd_2381514 : Nat := 4983230072969 + 3 ^ 40 * 2381514 * 2
def baseEnd_2381514 : Nat := 90582323511977818460935

theorem tailTrace_2381514 : CollatzResearch.WordTrace tailWord_2381514 prefixEnd_2381514 90582323511977818460935 := by
  unfold tailWord_2381514
  simp only [CollatzResearch.WordTrace]
  refine ⟨21715237873547245763715899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57907300996125988703242397 21715237873547245763715899)
  ·
    refine ⟨32572856810320868645573849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21715237873547245763715899 32572856810320868645573849)
    ·
      refine ⟨24429642607740651484180387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32572856810320868645573849 24429642607740651484180387)
      ·
        refine ⟨36644463911610977226270581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24429642607740651484180387 36644463911610977226270581)
        ·
          refine ⟨3435418491713529114962867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 36644463911610977226270581 3435418491713529114962867)
          ·
            refine ⟨5153127737570293672444301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3435418491713529114962867 5153127737570293672444301)
            ·
              refine ⟨1932422901588860127166613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5153127737570293672444301 1932422901588860127166613)
              ·
                refine ⟨90582323511977818460935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1932422901588860127166613 90582323511977818460935)
                ·
                  rfl

theorem cell22_2381514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 3, 6].length) (baseStart_2381514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381514 prefixEnd_2381514 := by exact prefixLift 2381514
  have htrace : WordTrace (prefixWord ++ tailWord_2381514) baseStart_2381514 baseEnd_2381514 := by
    simpa [prefixWord, tailWord_2381514, baseEnd_2381514] using wordTrace_append hprefix tailTrace_2381514
  have hstable : (prefixWord ++ tailWord_2381514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381514).length < 2 ^ (prefixWord ++ tailWord_2381514).sum := by decide
  have hdescent : baseEnd_2381514 < baseStart_2381514 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381516 : List Nat := [2, 2, 1, 5, 2, 2, 1, 1, 2, 4]
def baseStart_2381516 : Nat := 118140960795 + 2381516 * 2 ^ 59
def prefixEnd_2381516 : Nat := 4983230072969 + 3 ^ 40 * 2381516 * 2
def baseEnd_2381516 : Nat := 815241596248673027598409

theorem tailTrace_2381516 : CollatzResearch.WordTrace tailWord_2381516 prefixEnd_2381516 815241596248673027598409 := by
  unfold tailWord_2381516
  simp only [CollatzResearch.WordTrace]
  refine ⟨43430512220090868698218201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57907349626787824930957601 43430512220090868698218201)
  ·
    refine ⟨32572884165068151523663651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43430512220090868698218201 32572884165068151523663651)
    ·
      refine ⟨48859326247602227285495477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32572884165068151523663651 48859326247602227285495477)
      ·
        refine ⟨4580561835712708808015201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48859326247602227285495477 4580561835712708808015201)
        ·
          refine ⟨3435421376784531606011401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4580561835712708808015201 3435421376784531606011401)
          ·
            refine ⟨2576566032588398704508551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3435421376784531606011401 2576566032588398704508551)
            ·
              refine ⟨3864849048882598056762827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576566032588398704508551 3864849048882598056762827)
              ·
                refine ⟨5797273573323897085144241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3864849048882598056762827 5797273573323897085144241)
                ·
                  refine ⟨4347955179992922813858181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5797273573323897085144241 4347955179992922813858181)
                  ·
                    refine ⟨815241596248673027598409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4347955179992922813858181 815241596248673027598409)
                    ·
                      rfl

theorem cell22_2381516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 2, 1, 1, 2, 4].length) (baseStart_2381516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381516 prefixEnd_2381516 := by exact prefixLift 2381516
  have htrace : WordTrace (prefixWord ++ tailWord_2381516) baseStart_2381516 baseEnd_2381516 := by
    simpa [prefixWord, tailWord_2381516, baseEnd_2381516] using wordTrace_append hprefix tailTrace_2381516
  have hstable : (prefixWord ++ tailWord_2381516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381516).length < 2 ^ (prefixWord ++ tailWord_2381516).sum := by decide
  have hdescent : baseEnd_2381516 < baseStart_2381516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381546 : List Nat := [3, 1, 3, 1, 1, 1, 4, 4, 1, 3]
def baseStart_2381546 : Nat := 118140960795 + 2381546 * 2 ^ 59
def prefixEnd_2381546 : Nat := 4983230072969 + 3 ^ 40 * 2381546 * 2
def baseEnd_2381546 : Nat := 815251865861762949348317

theorem tailTrace_2381546 : CollatzResearch.WordTrace tailWord_2381546 prefixEnd_2381546 815251865861762949348317 := by
  unfold tailWord_2381546
  simp only [CollatzResearch.WordTrace]
  refine ⟨21715529657518263130007123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57908079086715368346685661 21715529657518263130007123)
  ·
    refine ⟨32573294486277394695010685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21715529657518263130007123 32573294486277394695010685)
    ·
      refine ⟨12214985432354023010629007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32573294486277394695010685 12214985432354023010629007)
      ·
        refine ⟨18322478148531034515943511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12214985432354023010629007 18322478148531034515943511)
        ·
          refine ⟨27483717222796551773915267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18322478148531034515943511 27483717222796551773915267)
          ·
            refine ⟨41225575834194827660872901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27483717222796551773915267 41225575834194827660872901)
            ·
              refine ⟨7729795468911530186413669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41225575834194827660872901 7729795468911530186413669)
              ·
                refine ⟨1449336650420911909952563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7729795468911530186413669 1449336650420911909952563)
                ·
                  refine ⟨2174004975631367864928845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449336650420911909952563 2174004975631367864928845)
                  ·
                    refine ⟨815251865861762949348317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2174004975631367864928845 815251865861762949348317)
                    ·
                      rfl

theorem cell22_2381546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_2381546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381546 prefixEnd_2381546 := by exact prefixLift 2381546
  have htrace : WordTrace (prefixWord ++ tailWord_2381546) baseStart_2381546 baseEnd_2381546 := by
    simpa [prefixWord, tailWord_2381546, baseEnd_2381546] using wordTrace_append hprefix tailTrace_2381546
  have hstable : (prefixWord ++ tailWord_2381546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381546).length < 2 ^ (prefixWord ++ tailWord_2381546).sum := by decide
  have hdescent : baseEnd_2381546 < baseStart_2381546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381589 : List Nat := [1, 3, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_2381589 : Nat := 118140960795 + 2381589 * 2 ^ 59
def prefixEnd_2381589 : Nat := 4983230072969 + 3 ^ 40 * 2381589 * 2
def baseEnd_2381589 : Nat := 815266585640525170523185

theorem tailTrace_2381589 : CollatzResearch.WordTrace tailWord_2381589 prefixEnd_2381589 815266585640525170523185 := by
  unfold tailWord_2381589
  simp only [CollatzResearch.WordTrace]
  refine ⟨86863686968917270863843821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57909124645944847242562547 86863686968917270863843821)
  ·
    refine ⟨32573882613343976573941433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86863686968917270863843821 32573882613343976573941433)
    ·
      refine ⟨24430411960007982430456075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32573882613343976573941433 24430411960007982430456075)
      ·
        refine ⟨36645617940011973645684113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24430411960007982430456075 36645617940011973645684113)
        ·
          refine ⟨27484213455008980234263085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36645617940011973645684113 27484213455008980234263085)
          ·
            refine ⟨10306580045628367587848657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27484213455008980234263085 10306580045628367587848657)
            ·
              refine ⟨7729935034221275690886493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10306580045628367587848657 7729935034221275690886493)
              ·
                refine ⟨2898725637832978384082435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7729935034221275690886493 2898725637832978384082435)
                ·
                  refine ⟨4348088456749467576123653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2898725637832978384082435 4348088456749467576123653)
                  ·
                    refine ⟨815266585640525170523185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4348088456749467576123653 815266585640525170523185)
                    ·
                      rfl

theorem cell22_2381589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_2381589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381589 prefixEnd_2381589 := by exact prefixLift 2381589
  have htrace : WordTrace (prefixWord ++ tailWord_2381589) baseStart_2381589 baseEnd_2381589 := by
    simpa [prefixWord, tailWord_2381589, baseEnd_2381589] using wordTrace_append hprefix tailTrace_2381589
  have hstable : (prefixWord ++ tailWord_2381589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381589).length < 2 ^ (prefixWord ++ tailWord_2381589).sum := by decide
  have hdescent : baseEnd_2381589 < baseStart_2381589 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381604 : List Nat := [2, 3, 1, 3, 2, 1, 3, 1, 6]
def baseStart_2381604 : Nat := 118140960795 + 2381604 * 2 ^ 59
def prefixEnd_2381604 : Nat := 4983230072969 + 3 ^ 40 * 2381604 * 2
def baseEnd_2381604 : Nat := 271757240149023377132713

theorem tailTrace_2381604 : CollatzResearch.WordTrace tailWord_2381604 prefixEnd_2381604 271757240149023377132713 := by
  unfold tailWord_2381604
  simp only [CollatzResearch.WordTrace]
  refine ⟨43432117031931464212819933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57909489375908618950426577 43432117031931464212819933)
  ·
    refine ⟨16287043886974299079807475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43432117031931464212819933 16287043886974299079807475)
    ·
      refine ⟨24430565830461448619711213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16287043886974299079807475 24430565830461448619711213)
      ·
        refine ⟨9161462186423043232391705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 24430565830461448619711213 9161462186423043232391705)
        ·
          refine ⟨6871096639817282424293779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9161462186423043232391705 6871096639817282424293779)
          ·
            refine ⟨10306644959725923636440669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6871096639817282424293779 10306644959725923636440669)
            ·
              refine ⟨3864991859897221363665251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10306644959725923636440669 3864991859897221363665251)
              ·
                refine ⟨5797487789845832045497877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3864991859897221363665251 5797487789845832045497877)
                ·
                  refine ⟨271757240149023377132713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5797487789845832045497877 271757240149023377132713)
                  ·
                    rfl

theorem cell22_2381604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_2381604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381604 prefixEnd_2381604 := by exact prefixLift 2381604
  have htrace : WordTrace (prefixWord ++ tailWord_2381604) baseStart_2381604 baseEnd_2381604 := by
    simpa [prefixWord, tailWord_2381604, baseEnd_2381604] using wordTrace_append hprefix tailTrace_2381604
  have hstable : (prefixWord ++ tailWord_2381604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381604).length < 2 ^ (prefixWord ++ tailWord_2381604).sum := by decide
  have hdescent : baseEnd_2381604 < baseStart_2381604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381655 : List Nat := [1, 1, 3, 2, 6, 1, 2, 2, 4]
def baseStart_2381655 : Nat := 118140960795 + 2381655 * 2 ^ 59
def prefixEnd_2381655 : Nat := 4983230072969 + 3 ^ 40 * 2381655 * 2
def baseEnd_2381655 : Nat := 271763059596440999457661

theorem tailTrace_2381655 : CollatzResearch.WordTrace tailWord_2381655 prefixEnd_2381655 271763059596440999457661 := by
  unfold tailWord_2381655
  simp only [CollatzResearch.WordTrace]
  refine ⟨86866094186678164135746419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57910729457785442757164279 86866094186678164135746419)
  ·
    refine ⟨130299141280017246203619629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86866094186678164135746419 130299141280017246203619629)
    ·
      refine ⟨48862177980006467326357361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130299141280017246203619629 48862177980006467326357361)
      ·
        refine ⟨36646633485004850494768021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48862177980006467326357361 36646633485004850494768021)
        ·
          refine ⟨1717810944609602366942251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36646633485004850494768021 1717810944609602366942251)
          ·
            refine ⟨2576716416914403550413377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717810944609602366942251 2576716416914403550413377)
            ·
              refine ⟨1932537312685802662810033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2576716416914403550413377 1932537312685802662810033)
              ·
                refine ⟨1449402984514351997107525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932537312685802662810033 1449402984514351997107525)
                ·
                  refine ⟨271763059596440999457661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1449402984514351997107525 271763059596440999457661)
                  ·
                    rfl

theorem cell22_2381655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2, 4].length) (baseStart_2381655 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381655 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381655 prefixEnd_2381655 := by exact prefixLift 2381655
  have htrace : WordTrace (prefixWord ++ tailWord_2381655) baseStart_2381655 baseEnd_2381655 := by
    simpa [prefixWord, tailWord_2381655, baseEnd_2381655] using wordTrace_append hprefix tailTrace_2381655
  have hstable : (prefixWord ++ tailWord_2381655).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381655).length < 2 ^ (prefixWord ++ tailWord_2381655).sum := by decide
  have hdescent : baseEnd_2381655 < baseStart_2381655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381666 : List Nat := [3, 3, 2, 1, 2, 3, 1, 7]
def baseStart_2381666 : Nat := 118140960795 + 2381666 * 2 ^ 59
def prefixEnd_2381666 : Nat := 4983230072969 + 3 ^ 40 * 2381666 * 2
def baseEnd_2381666 : Nat := 90588104923791404038661

theorem tailTrace_2381666 : CollatzResearch.WordTrace tailWord_2381666 prefixEnd_2381666 90588104923791404038661 := by
  unfold tailWord_2381666
  simp only [CollatzResearch.WordTrace]
  refine ⟨21716623847409578253599213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57910996926425542009597901 21716623847409578253599213)
  ·
    refine ⟨8143733942778591845099705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21716623847409578253599213 8143733942778591845099705)
    ·
      refine ⟨6107800457083943883824779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8143733942778591845099705 6107800457083943883824779)
      ·
        refine ⟨9161700685625915825737169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6107800457083943883824779 9161700685625915825737169)
        ·
          refine ⟨6871275514219436869302877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9161700685625915825737169 6871275514219436869302877)
          ·
            refine ⟨2576728317832288825988579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6871275514219436869302877 2576728317832288825988579)
            ·
              refine ⟨3865092476748433238982869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576728317832288825988579 3865092476748433238982869)
              ·
                refine ⟨90588104923791404038661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3865092476748433238982869 90588104923791404038661)
                ·
                  rfl

theorem cell22_2381666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 3, 1, 7].length) (baseStart_2381666 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381666 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381666 prefixEnd_2381666 := by exact prefixLift 2381666
  have htrace : WordTrace (prefixWord ++ tailWord_2381666) baseStart_2381666 baseEnd_2381666 := by
    simpa [prefixWord, tailWord_2381666, baseEnd_2381666] using wordTrace_append hprefix tailTrace_2381666
  have hstable : (prefixWord ++ tailWord_2381666).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381666).length < 2 ^ (prefixWord ++ tailWord_2381666).sum := by decide
  have hdescent : baseEnd_2381666 < baseStart_2381666 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381769 : List Nat := [1, 2, 1, 1, 2, 1, 2, 6, 2, 4]
def baseStart_2381769 : Nat := 118140960795 + 2381769 * 2 ^ 59
def prefixEnd_2381769 : Nat := 4983230072969 + 3 ^ 40 * 2381769 * 2
def baseEnd_2381769 : Nat := 815328203319064701022633

theorem tailTrace_2381769 : CollatzResearch.WordTrace tailWord_2381769 prefixEnd_2381769 815328203319064701022633 := by
  unfold tailWord_2381769
  simp only [CollatzResearch.WordTrace]
  refine ⟨86870252108265161605396361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57913501405510107736930907 86870252108265161605396361)
  ·
    refine ⟨65152689081198871204047271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86870252108265161605396361 65152689081198871204047271)
    ·
      refine ⟨97729033621798306806070907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65152689081198871204047271 97729033621798306806070907)
      ·
        refine ⟨146593550432697460209106361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97729033621798306806070907 146593550432697460209106361)
        ·
          refine ⟨109945162824523095156829771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146593550432697460209106361 109945162824523095156829771)
          ·
            refine ⟨164917744236784642735244657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 109945162824523095156829771 164917744236784642735244657)
            ·
              refine ⟨123688308177588482051433493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 164917744236784642735244657 123688308177588482051433493)
              ·
                refine ⟨5797889445824460096160945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123688308177588482051433493 5797889445824460096160945)
                ·
                  refine ⟨4348417084368345072120709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5797889445824460096160945 4348417084368345072120709)
                  ·
                    refine ⟨815328203319064701022633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4348417084368345072120709 815328203319064701022633)
                    ·
                      rfl

theorem cell22_2381769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_2381769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381769 prefixEnd_2381769 := by exact prefixLift 2381769
  have htrace : WordTrace (prefixWord ++ tailWord_2381769) baseStart_2381769 baseEnd_2381769 := by
    simpa [prefixWord, tailWord_2381769, baseEnd_2381769] using wordTrace_append hprefix tailTrace_2381769
  have hstable : (prefixWord ++ tailWord_2381769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381769).length < 2 ^ (prefixWord ++ tailWord_2381769).sum := by decide
  have hdescent : baseEnd_2381769 < baseStart_2381769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381771 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 2, 3]
def baseStart_2381771 : Nat := 118140960795 + 2381771 * 2 ^ 59
def prefixEnd_2381771 : Nat := 4983230072969 + 3 ^ 40 * 2381771 * 2
def baseEnd_2381771 : Nat := 815328887959937362472627

theorem tailTrace_2381771 : CollatzResearch.WordTrace tailWord_2381771 prefixEnd_2381771 815328887959937362472627 := by
  unfold tailWord_2381771
  simp only [CollatzResearch.WordTrace]
  refine ⟨86870325054257915946969167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57913550036171943964646111 86870325054257915946969167)
  ·
    refine ⟨130305487581386873920453751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86870325054257915946969167 130305487581386873920453751)
    ·
      refine ⟨195458231372080310880680627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130305487581386873920453751 195458231372080310880680627)
      ·
        refine ⟨293187347058120466321020941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195458231372080310880680627 293187347058120466321020941)
        ·
          refine ⟨109945255146795174870382853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293187347058120466321020941 109945255146795174870382853)
          ·
            refine ⟨20614735340024095288196785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 109945255146795174870382853 20614735340024095288196785)
            ·
              refine ⟨15461051505018071466147589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20614735340024095288196785 15461051505018071466147589)
              ·
                refine ⟨2898947157190888399902673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15461051505018071466147589 2898947157190888399902673)
                ·
                  refine ⟨2174210367893166299927005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2898947157190888399902673 2174210367893166299927005)
                  ·
                    refine ⟨815328887959937362472627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2174210367893166299927005 815328887959937362472627)
                    ·
                      rfl

theorem cell22_2381771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 2, 3].length) (baseStart_2381771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381771 prefixEnd_2381771 := by exact prefixLift 2381771
  have htrace : WordTrace (prefixWord ++ tailWord_2381771) baseStart_2381771 baseEnd_2381771 := by
    simpa [prefixWord, tailWord_2381771, baseEnd_2381771] using wordTrace_append hprefix tailTrace_2381771
  have hstable : (prefixWord ++ tailWord_2381771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381771).length < 2 ^ (prefixWord ++ tailWord_2381771).sum := by decide
  have hdescent : baseEnd_2381771 < baseStart_2381771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381784 : List Nat := [2, 1, 2, 2, 2, 2, 4, 7]
def baseStart_2381784 : Nat := 118140960795 + 2381784 * 2 ^ 59
def prefixEnd_2381784 : Nat := 4983230072969 + 3 ^ 40 * 2381784 * 2
def baseEnd_2381784 : Nat := 90592593125067740210843

theorem tailTrace_2381784 : CollatzResearch.WordTrace tailWord_2381784 prefixEnd_2381784 90592593125067740210843 := by
  unfold tailWord_2381784
  simp only [CollatzResearch.WordTrace]
  refine ⟨43435399601605409583596203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57913866135473879444794937 43435399601605409583596203)
  ·
    refine ⟨65153099402408114375394305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43435399601605409583596203 65153099402408114375394305)
    ·
      refine ⟨48864824551806085781545729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65153099402408114375394305 48864824551806085781545729)
      ·
        refine ⟨36648618413854564336159297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48864824551806085781545729 36648618413854564336159297)
        ·
          refine ⟨27486463810390923252119473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36648618413854564336159297 27486463810390923252119473)
          ·
            refine ⟨20614847857793192439089605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27486463810390923252119473 20614847857793192439089605)
            ·
              refine ⟨3865283973336223582329301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20614847857793192439089605 3865283973336223582329301)
              ·
                refine ⟨90592593125067740210843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3865283973336223582329301 90592593125067740210843)
                ·
                  rfl

theorem cell22_2381784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 7].length) (baseStart_2381784 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381784 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381784 prefixEnd_2381784 := by exact prefixLift 2381784
  have htrace : WordTrace (prefixWord ++ tailWord_2381784) baseStart_2381784 baseEnd_2381784 := by
    simpa [prefixWord, tailWord_2381784, baseEnd_2381784] using wordTrace_append hprefix tailTrace_2381784
  have hstable : (prefixWord ++ tailWord_2381784).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381784).length < 2 ^ (prefixWord ++ tailWord_2381784).sum := by decide
  have hdescent : baseEnd_2381784 < baseStart_2381784 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381880 : List Nat := [2, 1, 2, 1, 7, 1, 1, 2, 5]
def baseStart_2381880 : Nat := 118140960795 + 2381880 * 2 ^ 59
def prefixEnd_2381880 : Nat := 4983230072969 + 3 ^ 40 * 2381880 * 2
def baseEnd_2381880 : Nat := 271788733629165803832431

theorem tailTrace_2381880 : CollatzResearch.WordTrace tailWord_2381880 prefixEnd_2381880 271788733629165803832431 := by
  unfold tailWord_2381880
  simp only [CollatzResearch.WordTrace]
  refine ⟨43437150305431513781343547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57916200407242018375124729 43437150305431513781343547)
  ·
    refine ⟨65155725458147270672015321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43437150305431513781343547 65155725458147270672015321)
    ·
      refine ⟨48866794093610453004011491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65155725458147270672015321 48866794093610453004011491)
      ·
        refine ⟨73300191140415679506017237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48866794093610453004011491 73300191140415679506017237)
        ·
          refine ⟨1717973229853492488422279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 73300191140415679506017237 1717973229853492488422279)
          ·
            refine ⟨2576959844780238732633419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1717973229853492488422279 2576959844780238732633419)
            ·
              refine ⟨3865439767170358098950129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2576959844780238732633419 3865439767170358098950129)
              ·
                refine ⟨2899079825377768574212597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3865439767170358098950129 2899079825377768574212597)
                ·
                  refine ⟨271788733629165803832431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2899079825377768574212597 271788733629165803832431)
                  ·
                    rfl

theorem cell22_2381880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 7, 1, 1, 2, 5].length) (baseStart_2381880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381880 prefixEnd_2381880 := by exact prefixLift 2381880
  have htrace : WordTrace (prefixWord ++ tailWord_2381880) baseStart_2381880 baseEnd_2381880 := by
    simpa [prefixWord, tailWord_2381880, baseEnd_2381880] using wordTrace_append hprefix tailTrace_2381880
  have hstable : (prefixWord ++ tailWord_2381880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381880).length < 2 ^ (prefixWord ++ tailWord_2381880).sum := by decide
  have hdescent : baseEnd_2381880 < baseStart_2381880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381918 : List Nat := [4, 4, 1, 1, 3, 1, 1, 3, 1, 3]
def baseStart_2381918 : Nat := 118140960795 + 2381918 * 2 ^ 59
def prefixEnd_2381918 : Nat := 4983230072969 + 3 ^ 40 * 2381918 * 2
def baseEnd_2381918 : Nat := 815379209064077979047177

theorem tailTrace_2381918 : CollatzResearch.WordTrace tailWord_2381918 prefixEnd_2381918 815379209064077979047177 := by
  unfold tailWord_2381918
  simp only [CollatzResearch.WordTrace]
  refine ⟨10859460823090670006571301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57917124389816906701713605 10859460823090670006571301)
  ·
    refine ⟨2036148904329500626232119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10859460823090670006571301 2036148904329500626232119)
    ·
      refine ⟨3054223356494250939348179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2036148904329500626232119 3054223356494250939348179)
      ·
        refine ⟨4581335034741376409022269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3054223356494250939348179 4581335034741376409022269)
        ·
          refine ⟨1718000638028016153383351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4581335034741376409022269 1718000638028016153383351)
          ·
            refine ⟨2577000957042024230075027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1718000638028016153383351 2577000957042024230075027)
            ·
              refine ⟨3865501435563036345112541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577000957042024230075027 3865501435563036345112541)
              ·
                refine ⟨1449563038336138629417203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3865501435563036345112541 1449563038336138629417203)
                ·
                  refine ⟨2174344557504207944125805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449563038336138629417203 2174344557504207944125805)
                  ·
                    refine ⟨815379209064077979047177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2174344557504207944125805 815379209064077979047177)
                    ·
                      rfl

theorem cell22_2381918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_2381918 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381918 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381918 prefixEnd_2381918 := by exact prefixLift 2381918
  have htrace : WordTrace (prefixWord ++ tailWord_2381918) baseStart_2381918 baseEnd_2381918 := by
    simpa [prefixWord, tailWord_2381918, baseEnd_2381918] using wordTrace_append hprefix tailTrace_2381918
  have hstable : (prefixWord ++ tailWord_2381918).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381918).length < 2 ^ (prefixWord ++ tailWord_2381918).sum := by decide
  have hdescent : baseEnd_2381918 < baseStart_2381918 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381921 : List Nat := [1, 2, 3, 1, 1, 2, 1, 5, 2, 4]
def baseStart_2381921 : Nat := 118140960795 + 2381921 * 2 ^ 59
def prefixEnd_2381921 : Nat := 4983230072969 + 3 ^ 40 * 2381921 * 2
def baseEnd_2381921 : Nat := 815380236025386971222167

theorem tailTrace_2381921 : CollatzResearch.WordTrace tailWord_2381921 prefixEnd_2381921 815380236025386971222167 := by
  unfold tailWord_2381921
  simp only [CollatzResearch.WordTrace]
  refine ⟨86875796003714491564929617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57917197335809661043286411 86875796003714491564929617)
  ·
    refine ⟨65156847002785868673697213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86875796003714491564929617 65156847002785868673697213)
    ·
      refine ⟨24433817626044700752636455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65156847002785868673697213 24433817626044700752636455)
      ·
        refine ⟨36650726439067051128954683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24433817626044700752636455 36650726439067051128954683)
        ·
          refine ⟨54976089658600576693432025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36650726439067051128954683 54976089658600576693432025)
          ·
            refine ⟨41232067243950432520074019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 54976089658600576693432025 41232067243950432520074019)
            ·
              refine ⟨61848100865925648780111029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41232067243950432520074019 61848100865925648780111029)
              ·
                refine ⟨5798259456180529573135409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61848100865925648780111029 5798259456180529573135409)
                ·
                  refine ⟨4348694592135397179851557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5798259456180529573135409 4348694592135397179851557)
                  ·
                    refine ⟨815380236025386971222167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4348694592135397179851557 815380236025386971222167)
                    ·
                      rfl

theorem cell22_2381921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_2381921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381921 prefixEnd_2381921 := by exact prefixLift 2381921
  have htrace : WordTrace (prefixWord ++ tailWord_2381921) baseStart_2381921 baseEnd_2381921 := by
    simpa [prefixWord, tailWord_2381921, baseEnd_2381921] using wordTrace_append hprefix tailTrace_2381921
  have hstable : (prefixWord ++ tailWord_2381921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381921).length < 2 ^ (prefixWord ++ tailWord_2381921).sum := by decide
  have hdescent : baseEnd_2381921 < baseStart_2381921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381925 : List Nat := [1, 3, 1, 3, 2, 4, 1, 3, 4]
def baseStart_2381925 : Nat := 118140960795 + 2381925 * 2 ^ 59
def prefixEnd_2381925 : Nat := 4983230072969 + 3 ^ 40 * 2381925 * 2
def baseEnd_2381925 : Nat := 271793868435710764707385

theorem tailTrace_2381925 : CollatzResearch.WordTrace tailWord_2381925 prefixEnd_2381925 271793868435710764707385 := by
  unfold tailWord_2381925
  simp only [CollatzResearch.WordTrace]
  refine ⟨86875941895700000248075229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57917294597133333498716819 86875941895700000248075229)
  ·
    refine ⟨32578478210887500093028211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86875941895700000248075229 32578478210887500093028211)
    ·
      refine ⟨48867717316331250139542317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32578478210887500093028211 48867717316331250139542317)
      ·
        refine ⟨18325393993624218802328369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48867717316331250139542317 18325393993624218802328369)
        ·
          refine ⟨13744045495218164101746277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18325393993624218802328369 13744045495218164101746277)
          ·
            refine ⟨2577008530353405769077427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13744045495218164101746277 2577008530353405769077427)
            ·
              refine ⟨3865512795530108653616141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577008530353405769077427 3865512795530108653616141)
              ·
                refine ⟨1449567298323790745106053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3865512795530108653616141 1449567298323790745106053)
                ·
                  refine ⟨271793868435710764707385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1449567298323790745106053 271793868435710764707385)
                  ·
                    rfl

theorem cell22_2381925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 3, 4].length) (baseStart_2381925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381925 prefixEnd_2381925 := by exact prefixLift 2381925
  have htrace : WordTrace (prefixWord ++ tailWord_2381925) baseStart_2381925 baseEnd_2381925 := by
    simpa [prefixWord, tailWord_2381925, baseEnd_2381925] using wordTrace_append hprefix tailTrace_2381925
  have hstable : (prefixWord ++ tailWord_2381925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381925).length < 2 ^ (prefixWord ++ tailWord_2381925).sum := by decide
  have hdescent : baseEnd_2381925 < baseStart_2381925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381936 : List Nat := [2, 1, 1, 1, 5, 4, 8]
def baseStart_2381936 : Nat := 118140960795 + 2381936 * 2 ^ 59
def prefixEnd_2381936 : Nat := 4983230072969 + 3 ^ 40 * 2381936 * 2
def baseEnd_2381936 : Nat := 30199458178960441929523

theorem tailTrace_2381936 : CollatzResearch.WordTrace tailWord_2381936 prefixEnd_2381936 30199458178960441929523 := by
  unfold tailWord_2381936
  simp only [CollatzResearch.WordTrace]
  refine ⟨43438171549330074563362831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57917562065773432751150441 43438171549330074563362831)
  ·
    refine ⟨65157257323995111845044247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43438171549330074563362831 65157257323995111845044247)
    ·
      refine ⟨97735885985992667767566371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65157257323995111845044247 97735885985992667767566371)
      ·
        refine ⟨146603828978989001651349557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97735885985992667767566371 146603828978989001651349557)
        ·
          refine ⟨13744108966780218904814021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 146603828978989001651349557 13744108966780218904814021)
          ·
            refine ⟨2577020431271291044652629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13744108966780218904814021 2577020431271291044652629)
            ·
              refine ⟨30199458178960441929523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2577020431271291044652629 30199458178960441929523)
              ·
                rfl

theorem cell22_2381936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 8].length) (baseStart_2381936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381936 prefixEnd_2381936 := by exact prefixLift 2381936
  have htrace : WordTrace (prefixWord ++ tailWord_2381936) baseStart_2381936 baseEnd_2381936 := by
    simpa [prefixWord, tailWord_2381936, baseEnd_2381936] using wordTrace_append hprefix tailTrace_2381936
  have hstable : (prefixWord ++ tailWord_2381936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381936).length < 2 ^ (prefixWord ++ tailWord_2381936).sum := by decide
  have hdescent : baseEnd_2381936 < baseStart_2381936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381938 : List Nat := [3, 2, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_2381938 : Nat := 118140960795 + 2381938 * 2 ^ 59
def prefixEnd_2381938 : Nat := 4983230072969 + 3 ^ 40 * 2381938 * 2
def baseEnd_2381938 : Nat := 815386055472804593547115

theorem tailTrace_2381938 : CollatzResearch.WordTrace tailWord_2381938 prefixEnd_2381938 815386055472804593547115 := by
  unfold tailWord_2381938
  simp only [CollatzResearch.WordTrace]
  refine ⟨21719104011163225867074617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57917610696435268978865645 21719104011163225867074617)
  ·
    refine ⟨16289328008372419400305963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21719104011163225867074617 16289328008372419400305963)
    ·
      refine ⟨24433992012558629100458945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16289328008372419400305963 24433992012558629100458945)
      ·
        refine ⟨18325494009418971825344209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24433992012558629100458945 18325494009418971825344209)
        ·
          refine ⟨13744120507064228869008157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18325494009418971825344209 13744120507064228869008157)
          ·
            refine ⟨5154045190149085825878059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13744120507064228869008157 5154045190149085825878059)
            ·
              refine ⟨7731067785223628738817089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5154045190149085825878059 7731067785223628738817089)
              ·
                refine ⟨5798300838917721554112817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7731067785223628738817089 5798300838917721554112817)
                ·
                  refine ⟨4348725629188291165584613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5798300838917721554112817 4348725629188291165584613)
                  ·
                    refine ⟨815386055472804593547115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4348725629188291165584613 815386055472804593547115)
                    ·
                      rfl

theorem cell22_2381938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_2381938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381938 prefixEnd_2381938 := by exact prefixLift 2381938
  have htrace : WordTrace (prefixWord ++ tailWord_2381938) baseStart_2381938 baseEnd_2381938 := by
    simpa [prefixWord, tailWord_2381938, baseEnd_2381938] using wordTrace_append hprefix tailTrace_2381938
  have hstable : (prefixWord ++ tailWord_2381938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381938).length < 2 ^ (prefixWord ++ tailWord_2381938).sum := by decide
  have hdescent : baseEnd_2381938 < baseStart_2381938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381942 : List Nat := [5, 1, 1, 2, 1, 3, 3, 2, 4]
def baseStart_2381942 : Nat := 118140960795 + 2381942 * 2 ^ 59
def prefixEnd_2381942 : Nat := 4983230072969 + 3 ^ 40 * 2381942 * 2
def baseEnd_2381942 : Nat := 271795808251516638815701

theorem tailTrace_2381942 : CollatzResearch.WordTrace tailWord_2381942 prefixEnd_2381942 271795808251516638815701 := by
  unfold tailWord_2381942
  simp only [CollatzResearch.WordTrace]
  refine ⟨5429785121039900759465255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57917707957758941434296053 5429785121039900759465255)
  ·
    refine ⟨8144677681559851139197883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5429785121039900759465255 8144677681559851139197883)
    ·
      refine ⟨12217016522339776708796825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8144677681559851139197883 12217016522339776708796825)
      ·
        refine ⟨9162762391754832531597619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12217016522339776708796825 9162762391754832531597619)
        ·
          refine ⟨13744143587632248797396429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9162762391754832531597619 13744143587632248797396429)
          ·
            refine ⟨5154053845362093299023661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13744143587632248797396429 5154053845362093299023661)
            ·
              refine ⟨1932770192010784987133873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5154053845362093299023661 1932770192010784987133873)
              ·
                refine ⟨1449577644008088740350405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1932770192010784987133873 1449577644008088740350405)
                ·
                  refine ⟨271795808251516638815701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1449577644008088740350405 271795808251516638815701)
                  ·
                    rfl

theorem cell22_2381942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 3, 2, 4].length) (baseStart_2381942 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381942 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381942 prefixEnd_2381942 := by exact prefixLift 2381942
  have htrace : WordTrace (prefixWord ++ tailWord_2381942) baseStart_2381942 baseEnd_2381942 := by
    simpa [prefixWord, tailWord_2381942, baseEnd_2381942] using wordTrace_append hprefix tailTrace_2381942
  have hstable : (prefixWord ++ tailWord_2381942).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381942).length < 2 ^ (prefixWord ++ tailWord_2381942).sum := by decide
  have hdescent : baseEnd_2381942 < baseStart_2381942 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381953 : List Nat := [1, 2, 4, 2, 3, 1, 2, 7]
def baseStart_2381953 : Nat := 118140960795 + 2381953 * 2 ^ 59
def prefixEnd_2381953 : Nat := 4983230072969 + 3 ^ 40 * 2381953 * 2
def baseEnd_2381953 : Nat := 90599021142149950491341

theorem tailTrace_2381953 : CollatzResearch.WordTrace tailWord_2381953 prefixEnd_2381953 90599021142149950491341 := by
  unfold tailWord_2381953
  simp only [CollatzResearch.WordTrace]
  refine ⟨86876963139598561030094513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57917975426399040686729675 86876963139598561030094513)
  ·
    refine ⟨65157722354698920772570885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86876963139598561030094513 65157722354698920772570885)
    ·
      refine ⟨12217072941506047644857041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65157722354698920772570885 12217072941506047644857041)
      ·
        refine ⟨9162804706129535733642781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12217072941506047644857041 9162804706129535733642781)
        ·
          refine ⟨3436051764798575900116043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9162804706129535733642781 3436051764798575900116043)
          ·
            refine ⟨5154077647197863850174065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436051764798575900116043 5154077647197863850174065)
            ·
              refine ⟨3865558235398397887630549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5154077647197863850174065 3865558235398397887630549)
              ·
                refine ⟨90599021142149950491341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3865558235398397887630549 90599021142149950491341)
                ·
                  rfl

theorem cell22_2381953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 1, 2, 7].length) (baseStart_2381953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381953 prefixEnd_2381953 := by exact prefixLift 2381953
  have htrace : WordTrace (prefixWord ++ tailWord_2381953) baseStart_2381953 baseEnd_2381953 := by
    simpa [prefixWord, tailWord_2381953, baseEnd_2381953] using wordTrace_append hprefix tailTrace_2381953
  have hstable : (prefixWord ++ tailWord_2381953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381953).length < 2 ^ (prefixWord ++ tailWord_2381953).sum := by decide
  have hdescent : baseEnd_2381953 < baseStart_2381953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381957 : List Nat := [1, 3, 1, 1, 5, 3, 2, 1, 2, 3]
def baseStart_2381957 : Nat := 118140960795 + 2381957 * 2 ^ 59
def prefixEnd_2381957 : Nat := 4983230072969 + 3 ^ 40 * 2381957 * 2
def baseEnd_2381957 : Nat := 815392559561094877322057

theorem tailTrace_2381957 : CollatzResearch.WordTrace tailWord_2381957 prefixEnd_2381957 815392559561094877322057 := by
  unfold tailWord_2381957
  simp only [CollatzResearch.WordTrace]
  refine ⟨86877109031584069713240125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57918072687722713142160083 86877109031584069713240125)
  ·
    refine ⟨32578915886844026142465047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86877109031584069713240125 32578915886844026142465047)
    ·
      refine ⟨48868373830266039213697571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32578915886844026142465047 48868373830266039213697571)
      ·
        refine ⟨73302560745399058820546357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48868373830266039213697571 73302560745399058820546357)
        ·
          refine ⟨6872115069881161764426221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 73302560745399058820546357 6872115069881161764426221)
          ·
            refine ⟨2577043151205435661659833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6872115069881161764426221 2577043151205435661659833)
            ·
              refine ⟨1932782363404076746244875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2577043151205435661659833 1932782363404076746244875)
              ·
                refine ⟨2899173545106115119367313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1932782363404076746244875 2899173545106115119367313)
                ·
                  refine ⟨2174380158829586339525485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2899173545106115119367313 2174380158829586339525485)
                  ·
                    refine ⟨815392559561094877322057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2174380158829586339525485 815392559561094877322057)
                    ·
                      rfl

theorem cell22_2381957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_2381957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381957 prefixEnd_2381957 := by exact prefixLift 2381957
  have htrace : WordTrace (prefixWord ++ tailWord_2381957) baseStart_2381957 baseEnd_2381957 := by
    simpa [prefixWord, tailWord_2381957, baseEnd_2381957] using wordTrace_append hprefix tailTrace_2381957
  have hstable : (prefixWord ++ tailWord_2381957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381957).length < 2 ^ (prefixWord ++ tailWord_2381957).sum := by decide
  have hdescent : baseEnd_2381957 < baseStart_2381957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2381972 : List Nat := [2, 4, 2, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2381972 : Nat := 118140960795 + 2381972 * 2 ^ 59
def prefixEnd_2381972 : Nat := 4983230072969 + 3 ^ 40 * 2381972 * 2
def baseEnd_2381972 : Nat := 815397694367639838197011

theorem tailTrace_2381972 : CollatzResearch.WordTrace tailWord_2381972 prefixEnd_2381972 815397694367639838197011 := by
  unfold tailWord_2381972
  simp only [CollatzResearch.WordTrace]
  refine ⟨43438828063264863637518085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57918437417686484850024113 43438828063264863637518085)
  ·
    refine ⟨8144780261862161932034641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43438828063264863637518085 8144780261862161932034641)
    ·
      refine ⟨6108585196396621449025981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8144780261862161932034641 6108585196396621449025981)
      ·
        refine ⟨2290719448648733043384743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6108585196396621449025981 2290719448648733043384743)
        ·
          refine ⟨3436079172973099565077115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290719448648733043384743 3436079172973099565077115)
          ·
            refine ⟨5154118759459649347615673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3436079172973099565077115 5154118759459649347615673)
            ·
              refine ⟨3865589069594737010711755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5154118759459649347615673 3865589069594737010711755)
              ·
                refine ⟨5798383604392105516067633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3865589069594737010711755 5798383604392105516067633)
                ·
                  refine ⟨4348787703294079137050725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5798383604392105516067633 4348787703294079137050725)
                  ·
                    refine ⟨815397694367639838197011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4348787703294079137050725 815397694367639838197011)
                    ·
                      rfl

theorem cell22_2381972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2381972 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2381972 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2381972 prefixEnd_2381972 := by exact prefixLift 2381972
  have htrace : WordTrace (prefixWord ++ tailWord_2381972) baseStart_2381972 baseEnd_2381972 := by
    simpa [prefixWord, tailWord_2381972, baseEnd_2381972] using wordTrace_append hprefix tailTrace_2381972
  have hstable : (prefixWord ++ tailWord_2381972).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2381972).length < 2 ^ (prefixWord ++ tailWord_2381972).sum := by decide
  have hdescent : baseEnd_2381972 < baseStart_2381972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2381972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382004 : List Nat := [2, 5, 3, 1, 1, 2, 1, 7]
def baseStart_2382004 : Nat := 118140960795 + 2382004 * 2 ^ 59
def prefixEnd_2382004 : Nat := 4983230072969 + 3 ^ 40 * 2382004 * 2
def baseEnd_2382004 : Nat := 90600960957955824599657

theorem tailTrace_2382004 : CollatzResearch.WordTrace tailWord_2382004 prefixEnd_2382004 90600960957955824599657 := by
  unfold tailWord_2382004
  simp only [CollatzResearch.WordTrace]
  refine ⟨43439411631206898370100533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57919215508275864493467377 43439411631206898370100533)
  ·
    refine ⟨4072444840425646722196925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43439411631206898370100533 4072444840425646722196925)
    ·
      refine ⟨1527166815159617520823847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4072444840425646722196925 1527166815159617520823847)
      ·
        refine ⟨2290750222739426281235771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527166815159617520823847 2290750222739426281235771)
        ·
          refine ⟨3436125334109139421853657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2290750222739426281235771 3436125334109139421853657)
          ·
            refine ⟨2577094000581854566390243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3436125334109139421853657 2577094000581854566390243)
            ·
              refine ⟨3865641000872781849585365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577094000581854566390243 3865641000872781849585365)
              ·
                refine ⟨90600960957955824599657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3865641000872781849585365 90600960957955824599657)
                ·
                  rfl

theorem cell22_2382004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 2, 1, 7].length) (baseStart_2382004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382004 prefixEnd_2382004 := by exact prefixLift 2382004
  have htrace : WordTrace (prefixWord ++ tailWord_2382004) baseStart_2382004 baseEnd_2382004 := by
    simpa [prefixWord, tailWord_2382004, baseEnd_2382004] using wordTrace_append hprefix tailTrace_2382004
  have hstable : (prefixWord ++ tailWord_2382004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382004).length < 2 ^ (prefixWord ++ tailWord_2382004).sum := by decide
  have hdescent : baseEnd_2382004 < baseStart_2382004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382011 : List Nat := [1, 1, 1, 1, 1, 2, 5, 1, 5, 4]
def baseStart_2382011 : Nat := 118140960795 + 2382011 * 2 ^ 59
def prefixEnd_2382011 : Nat := 4983230072969 + 3 ^ 40 * 2382011 * 2
def baseEnd_2382011 : Nat := 815411044864656736471891

theorem tailTrace_2382011 : CollatzResearch.WordTrace tailWord_2382011 prefixEnd_2382011 815411044864656736471891 := by
  unfold tailWord_2382011
  simp only [CollatzResearch.WordTrace]
  refine ⟨86879078573388436935705887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57919385715592291290470591 86879078573388436935705887)
  ·
    refine ⟨130318617860082655403558831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86879078573388436935705887 130318617860082655403558831)
    ·
      refine ⟨195477926790123983105338247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130318617860082655403558831 195477926790123983105338247)
      ·
        refine ⟨293216890185185974658007371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195477926790123983105338247 293216890185185974658007371)
        ·
          refine ⟨439825335277778961987011057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293216890185185974658007371 439825335277778961987011057)
          ·
            refine ⟨329869001458334221490258293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 439825335277778961987011057 329869001458334221490258293)
            ·
              refine ⟨30925218886718833264711715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 329869001458334221490258293 30925218886718833264711715)
              ·
                refine ⟨46387828330078249897067573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30925218886718833264711715 46387828330078249897067573)
                ·
                  refine ⟨4348858905944835927850085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 46387828330078249897067573 4348858905944835927850085)
                  ·
                    refine ⟨815411044864656736471891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4348858905944835927850085 815411044864656736471891)
                    ·
                      rfl

theorem cell22_2382011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 1, 5, 4].length) (baseStart_2382011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382011 prefixEnd_2382011 := by exact prefixLift 2382011
  have htrace : WordTrace (prefixWord ++ tailWord_2382011) baseStart_2382011 baseEnd_2382011 := by
    simpa [prefixWord, tailWord_2382011, baseEnd_2382011] using wordTrace_append hprefix tailTrace_2382011
  have hstable : (prefixWord ++ tailWord_2382011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382011).length < 2 ^ (prefixWord ++ tailWord_2382011).sum := by decide
  have hdescent : baseEnd_2382011 < baseStart_2382011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382043 : List Nat := [1, 1, 1, 1, 1, 1, 1, 11, 4]
def baseStart_2382043 : Nat := 118140960795 + 2382043 * 2 ^ 59
def prefixEnd_2382043 : Nat := 4983230072969 + 3 ^ 40 * 2382043 * 2
def baseEnd_2382043 : Nat := 271807333039539773223931

theorem tailTrace_2382043 : CollatzResearch.WordTrace tailWord_2382043 prefixEnd_2382043 271807333039539773223931 := by
  unfold tailWord_2382043
  simp only [CollatzResearch.WordTrace]
  refine ⟨86880245709272506400870783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57920163806181670933913855 86880245709272506400870783)
  ·
    refine ⟨130320368563908759601306175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86880245709272506400870783 130320368563908759601306175)
    ·
      refine ⟨195480552845863139401959263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130320368563908759601306175 195480552845863139401959263)
      ·
        refine ⟨293220829268794709102938895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195480552845863139401959263 293220829268794709102938895)
        ·
          refine ⟨439831243903192063654408343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293220829268794709102938895 439831243903192063654408343)
          ·
            refine ⟨659746865854788095481612515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 439831243903192063654408343 659746865854788095481612515)
            ·
              refine ⟨989620298782182143222418773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 659746865854788095481612515 989620298782182143222418773)
              ·
                refine ⟨1449639109544212123860965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 989620298782182143222418773 1449639109544212123860965)
                ·
                  refine ⟨271807333039539773223931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1449639109544212123860965 271807333039539773223931)
                  ·
                    rfl

theorem cell22_2382043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 11, 4].length) (baseStart_2382043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382043 prefixEnd_2382043 := by exact prefixLift 2382043
  have htrace : WordTrace (prefixWord ++ tailWord_2382043) baseStart_2382043 baseEnd_2382043 := by
    simpa [prefixWord, tailWord_2382043, baseEnd_2382043] using wordTrace_append hprefix tailTrace_2382043
  have hstable : (prefixWord ++ tailWord_2382043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382043).length < 2 ^ (prefixWord ++ tailWord_2382043).sum := by decide
  have hdescent : baseEnd_2382043 < baseStart_2382043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382088 : List Nat := [2, 1, 3, 2, 3, 2, 1, 8]
def baseStart_2382088 : Nat := 118140960795 + 2382088 * 2 ^ 59
def prefixEnd_2382088 : Nat := 4983230072969 + 3 ^ 40 * 2382088 * 2
def baseEnd_2382088 : Nat := 90604155948694911366295

theorem tailTrace_2382088 : CollatzResearch.WordTrace tailWord_2382088 prefixEnd_2382088 90604155948694911366295 := by
  unfold tailWord_2382088
  simp only [CollatzResearch.WordTrace]
  refine ⟨43440943497054739543129459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57921257996072986057505945 43440943497054739543129459)
  ·
    refine ⟨65161415245582109314694189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43440943497054739543129459 65161415245582109314694189)
    ·
      refine ⟨24435530717093290993010321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65161415245582109314694189 24435530717093290993010321)
      ·
        refine ⟨18326648037819968244757741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24435530717093290993010321 18326648037819968244757741)
        ·
          refine ⟨6872493014182488091784153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18326648037819968244757741 6872493014182488091784153)
          ·
            refine ⟨5154369760636866068838115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6872493014182488091784153 5154369760636866068838115)
            ·
              refine ⟨7731554640955299103257173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5154369760636866068838115 7731554640955299103257173)
              ·
                refine ⟨90604155948694911366295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7731554640955299103257173 90604155948694911366295)
                ·
                  rfl

theorem cell22_2382088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 8].length) (baseStart_2382088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382088 prefixEnd_2382088 := by exact prefixLift 2382088
  have htrace : WordTrace (prefixWord ++ tailWord_2382088) baseStart_2382088 baseEnd_2382088 := by
    simpa [prefixWord, tailWord_2382088, baseEnd_2382088] using wordTrace_append hprefix tailTrace_2382088
  have hstable : (prefixWord ++ tailWord_2382088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382088).length < 2 ^ (prefixWord ++ tailWord_2382088).sum := by decide
  have hdescent : baseEnd_2382088 < baseStart_2382088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382212 : List Nat := [2, 3, 2, 1, 1, 2, 4, 3, 4]
def baseStart_2382212 : Nat := 118140960795 + 2382212 * 2 ^ 59
def prefixEnd_2382212 : Nat := 4983230072969 + 3 ^ 40 * 2382212 * 2
def baseEnd_2382212 : Nat := 271826617090786404065425

theorem tailTrace_2382212 : CollatzResearch.WordTrace tailWord_2382212 prefixEnd_2382212 271826617090786404065425 := by
  unfold tailWord_2382212
  simp only [CollatzResearch.WordTrace]
  refine ⟨43443204822830124131886445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57924273097106832175848593 43443204822830124131886445)
  ·
    refine ⟨16291201808561296549457417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43443204822830124131886445 16291201808561296549457417)
    ·
      refine ⟨12218401356420972412093063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16291201808561296549457417 12218401356420972412093063)
      ·
        refine ⟨18327602034631458618139595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12218401356420972412093063 18327602034631458618139595)
        ·
          refine ⟨27491403051947187927209393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18327602034631458618139595 27491403051947187927209393)
          ·
            refine ⟨20618552288960390945407045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27491403051947187927209393 20618552288960390945407045)
            ·
              refine ⟨3865978554180073302263821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20618552288960390945407045 3865978554180073302263821)
              ·
                refine ⟨1449741957817527488348933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3865978554180073302263821 1449741957817527488348933)
                ·
                  refine ⟨271826617090786404065425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1449741957817527488348933 271826617090786404065425)
                  ·
                    rfl

theorem cell22_2382212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_2382212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382212 prefixEnd_2382212 := by exact prefixLift 2382212
  have htrace : WordTrace (prefixWord ++ tailWord_2382212) baseStart_2382212 baseEnd_2382212 := by
    simpa [prefixWord, tailWord_2382212, baseEnd_2382212] using wordTrace_append hprefix tailTrace_2382212
  have hstable : (prefixWord ++ tailWord_2382212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382212).length < 2 ^ (prefixWord ++ tailWord_2382212).sum := by decide
  have hdescent : baseEnd_2382212 < baseStart_2382212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382257 : List Nat := [1, 2, 2, 4, 1, 4, 2, 6]
def baseStart_2382257 : Nat := 118140960795 + 2382257 * 2 ^ 59
def prefixEnd_2382257 : Nat := 4983230072969 + 3 ^ 40 * 2382257 * 2
def baseEnd_2382257 : Nat := 90610583965777121646793

theorem tailTrace_2382257 : CollatzResearch.WordTrace tailWord_2382257 prefixEnd_2382257 90610583965777121646793 := by
  unfold tailWord_2382257
  simp only [CollatzResearch.WordTrace]
  refine ⟨86888050930497220949161025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57925367286998147299440683 86888050930497220949161025)
  ·
    refine ⟨65166038197872915711870769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86888050930497220949161025 65166038197872915711870769)
    ·
      refine ⟨48874528648404686783903077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65166038197872915711870769 48874528648404686783903077)
      ·
        refine ⟨9163974121575878771981827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48874528648404686783903077 9163974121575878771981827)
        ·
          refine ⟨13745961182363818157972741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9163974121575878771981827 13745961182363818157972741)
          ·
            refine ⟨2577367721693215904619889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13745961182363818157972741 2577367721693215904619889)
            ·
              refine ⟨1933025791269911928464917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2577367721693215904619889 1933025791269911928464917)
              ·
                refine ⟨90610583965777121646793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1933025791269911928464917 90610583965777121646793)
                ·
                  rfl

theorem cell22_2382257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 2, 6].length) (baseStart_2382257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382257 prefixEnd_2382257 := by exact prefixLift 2382257
  have htrace : WordTrace (prefixWord ++ tailWord_2382257) baseStart_2382257 baseEnd_2382257 := by
    simpa [prefixWord, tailWord_2382257, baseEnd_2382257] using wordTrace_append hprefix tailTrace_2382257
  have hstable : (prefixWord ++ tailWord_2382257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382257).length < 2 ^ (prefixWord ++ tailWord_2382257).sum := by decide
  have hdescent : baseEnd_2382257 < baseStart_2382257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382315 : List Nat := [1, 1, 1, 1, 2, 3, 5, 1, 3, 4]
def baseStart_2382315 : Nat := 118140960795 + 2382315 * 2 ^ 59
def prefixEnd_2382315 : Nat := 4983230072969 + 3 ^ 40 * 2382315 * 2
def baseEnd_2382315 : Nat := 815515110277301276870959

theorem tailTrace_2382315 : CollatzResearch.WordTrace tailWord_2382315 prefixEnd_2382315 815515110277301276870959 := by
  unfold tailWord_2382315
  simp only [CollatzResearch.WordTrace]
  refine ⟨86890166364287096854772399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57926777576191397903181599 86890166364287096854772399)
  ·
    refine ⟨130335249546430645282158599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86890166364287096854772399 130335249546430645282158599)
    ·
      refine ⟨195502874319645967923237899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130335249546430645282158599 195502874319645967923237899)
      ·
        refine ⟨293254311479468951884856849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195502874319645967923237899 293254311479468951884856849)
        ·
          refine ⟨219940733609601713913642637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293254311479468951884856849 219940733609601713913642637)
          ·
            refine ⟨82477775103600642717615989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 219940733609601713913642637 82477775103600642717615989)
            ·
              refine ⟨7732291415962560254776499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82477775103600642717615989 7732291415962560254776499)
              ·
                refine ⟨11598437123943840382164749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7732291415962560254776499 11598437123943840382164749)
                ·
                  refine ⟨4349413921478940143311781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11598437123943840382164749 4349413921478940143311781)
                  ·
                    refine ⟨815515110277301276870959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4349413921478940143311781 815515110277301276870959)
                    ·
                      rfl

theorem cell22_2382315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3, 4].length) (baseStart_2382315 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382315 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382315 prefixEnd_2382315 := by exact prefixLift 2382315
  have htrace : WordTrace (prefixWord ++ tailWord_2382315) baseStart_2382315 baseEnd_2382315 := by
    simpa [prefixWord, tailWord_2382315, baseEnd_2382315] using wordTrace_append hprefix tailTrace_2382315
  have hstable : (prefixWord ++ tailWord_2382315).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382315).length < 2 ^ (prefixWord ++ tailWord_2382315).sum := by decide
  have hdescent : baseEnd_2382315 < baseStart_2382315 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382396 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 2, 3]
def baseStart_2382396 : Nat := 118140960795 + 2382396 * 2 ^ 59
def prefixEnd_2382396 : Nat := 4983230072969 + 3 ^ 40 * 2382396 * 2
def baseEnd_2382396 : Nat := 815542838232644065595711

theorem tailTrace_2382396 : CollatzResearch.WordTrace tailWord_2382396 prefixEnd_2382396 815542838232644065595711 := by
  unfold tailWord_2382396
  simp only [CollatzResearch.WordTrace]
  refine ⟨43446560338496823844235521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57928747117995765125647361 43446560338496823844235521)
  ·
    refine ⟨32584920253872617883176641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43446560338496823844235521 32584920253872617883176641)
    ·
      refine ⟨24438690190404463412382481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32584920253872617883176641 24438690190404463412382481)
      ·
        refine ⟨18329017642803347559286861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24438690190404463412382481 18329017642803347559286861)
        ·
          refine ⟨6873381616051255334732573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18329017642803347559286861 6873381616051255334732573)
          ·
            refine ⟨2577518106019220750524715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6873381616051255334732573 2577518106019220750524715)
            ·
              refine ⟨3866277159028831125787073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577518106019220750524715 3866277159028831125787073)
              ·
                refine ⟨2899707869271623344340305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3866277159028831125787073 2899707869271623344340305)
                ·
                  refine ⟨2174780901953717508255229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2899707869271623344340305 2174780901953717508255229)
                  ·
                    refine ⟨815542838232644065595711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2174780901953717508255229 815542838232644065595711)
                    ·
                      rfl

theorem cell22_2382396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 2, 3].length) (baseStart_2382396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382396 prefixEnd_2382396 := by exact prefixLift 2382396
  have htrace : WordTrace (prefixWord ++ tailWord_2382396) baseStart_2382396 baseEnd_2382396 := by
    simpa [prefixWord, tailWord_2382396, baseEnd_2382396] using wordTrace_append hprefix tailTrace_2382396
  have hstable : (prefixWord ++ tailWord_2382396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382396).length < 2 ^ (prefixWord ++ tailWord_2382396).sum := by decide
  have hdescent : baseEnd_2382396 < baseStart_2382396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382413 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 2, 3]
def baseStart_2382413 : Nat := 118140960795 + 2382413 * 2 ^ 59
def prefixEnd_2382413 : Nat := 4983230072969 + 3 ^ 40 * 2382413 * 2
def baseEnd_2382413 : Nat := 815548657680061687920659

theorem tailTrace_2382413 : CollatzResearch.WordTrace tailWord_2382413 prefixEnd_2382413 815548657680061687920659 := by
  unfold tailWord_2382413
  simp only [CollatzResearch.WordTrace]
  refine ⟨86893740717932059591839893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57929160478621373061226595 86893740717932059591839893)
  ·
    refine ⟨4073144096153065293367495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 86893740717932059591839893 4073144096153065293367495)
    ·
      refine ⟨6109716144229597940051243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4073144096153065293367495 6109716144229597940051243)
      ·
        refine ⟨9164574216344396910076865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6109716144229597940051243 9164574216344396910076865)
        ·
          refine ⟨6873430662258297682557649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9164574216344396910076865 6873430662258297682557649)
          ·
            refine ⟨5155072996693723261918237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6873430662258297682557649 5155072996693723261918237)
            ·
              refine ⟨1933152373760146223219339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5155072996693723261918237 1933152373760146223219339)
              ·
                refine ⟨2899728560640219334829009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1933152373760146223219339 2899728560640219334829009)
                ·
                  refine ⟨2174796420480164501121757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2899728560640219334829009 2174796420480164501121757)
                  ·
                    refine ⟨815548657680061687920659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2174796420480164501121757 815548657680061687920659)
                    ·
                      rfl

theorem cell22_2382413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 2, 3].length) (baseStart_2382413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382413 prefixEnd_2382413 := by exact prefixLift 2382413
  have htrace : WordTrace (prefixWord ++ tailWord_2382413) baseStart_2382413 baseEnd_2382413 := by
    simpa [prefixWord, tailWord_2382413, baseEnd_2382413] using wordTrace_append hprefix tailTrace_2382413
  have hstable : (prefixWord ++ tailWord_2382413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382413).length < 2 ^ (prefixWord ++ tailWord_2382413).sum := by decide
  have hdescent : baseEnd_2382413 < baseStart_2382413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382527 : List Nat := [1, 1, 2, 2, 2, 4, 3, 7]
def baseStart_2382527 : Nat := 118140960795 + 2382527 * 2 ^ 59
def prefixEnd_2382527 : Nat := 4983230072969 + 3 ^ 40 * 2382527 * 2
def baseEnd_2382527 : Nat := 90620853578867043396701

theorem tailTrace_2382527 : CollatzResearch.WordTrace tailWord_2382527 prefixEnd_2382527 90620853578867043396701 := by
  unfold tailWord_2382527
  simp only [CollatzResearch.WordTrace]
  refine ⟨86897898639519057061489835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57931932426346038040993223 86897898639519057061489835)
  ·
    refine ⟨130346847959278585592234753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86897898639519057061489835 130346847959278585592234753)
    ·
      refine ⟨97760135969458939194176065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130346847959278585592234753 97760135969458939194176065)
      ·
        refine ⟨73320101977094204395632049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97760135969458939194176065 73320101977094204395632049)
        ·
          refine ⟨54990076482820653296724037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73320101977094204395632049 54990076482820653296724037)
          ·
            refine ⟨10310639340528872493135757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54990076482820653296724037 10310639340528872493135757)
            ·
              refine ⟨3866489752698327184925909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10310639340528872493135757 3866489752698327184925909)
              ·
                refine ⟨90620853578867043396701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3866489752698327184925909 90620853578867043396701)
                ·
                  rfl

theorem cell22_2382527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 3, 7].length) (baseStart_2382527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382527 prefixEnd_2382527 := by exact prefixLift 2382527
  have htrace : WordTrace (prefixWord ++ tailWord_2382527) baseStart_2382527 baseEnd_2382527 := by
    simpa [prefixWord, tailWord_2382527, baseEnd_2382527] using wordTrace_append hprefix tailTrace_2382527
  have hstable : (prefixWord ++ tailWord_2382527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382527).length < 2 ^ (prefixWord ++ tailWord_2382527).sum := by decide
  have hdescent : baseEnd_2382527 < baseStart_2382527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382576 : List Nat := [2, 1, 1, 1, 3, 1, 3, 6, 1, 3]
def baseStart_2382576 : Nat := 118140960795 + 2382576 * 2 ^ 59
def prefixEnd_2382576 : Nat := 4983230072969 + 3 ^ 40 * 2382576 * 2
def baseEnd_2382576 : Nat := 815604455911183596095159

theorem tailTrace_2382576 : CollatzResearch.WordTrace tailWord_2382576 prefixEnd_2382576 815604455911183596095159 := by
  unfold tailWord_2382576
  simp only [CollatzResearch.WordTrace]
  refine ⟨43449842908170769215011791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57933123877561025620015721 43449842908170769215011791)
  ·
    refine ⟨65174764362256153822517687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43449842908170769215011791 65174764362256153822517687)
    ·
      refine ⟨97762146543384230733776531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65174764362256153822517687 97762146543384230733776531)
      ·
        refine ⟨146643219815076346100664797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97762146543384230733776531 146643219815076346100664797)
        ·
          refine ⟨54991207430653629787749299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146643219815076346100664797 54991207430653629787749299)
          ·
            refine ⟨82486811145980444681623949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54991207430653629787749299 82486811145980444681623949)
            ·
              refine ⟨30932554179742666755608981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82486811145980444681623949 30932554179742666755608981)
              ·
                refine ⟨1449963477175437504169171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 30932554179742666755608981 1449963477175437504169171)
                ·
                  refine ⟨2174945215763156256253757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1449963477175437504169171 2174945215763156256253757)
                  ·
                    refine ⟨815604455911183596095159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2174945215763156256253757 815604455911183596095159)
                    ·
                      rfl

theorem cell22_2382576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 6, 1, 3].length) (baseStart_2382576 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382576 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382576 prefixEnd_2382576 := by exact prefixLift 2382576
  have htrace : WordTrace (prefixWord ++ tailWord_2382576) baseStart_2382576 baseEnd_2382576 := by
    simpa [prefixWord, tailWord_2382576, baseEnd_2382576] using wordTrace_append hprefix tailTrace_2382576
  have hstable : (prefixWord ++ tailWord_2382576).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382576).length < 2 ^ (prefixWord ++ tailWord_2382576).sum := by decide
  have hdescent : baseEnd_2382576 < baseStart_2382576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382696 : List Nat := [2, 1, 4, 2, 1, 4, 1, 7]
def baseStart_2382696 : Nat := 118140960795 + 2382696 * 2 ^ 59
def prefixEnd_2382696 : Nat := 4983230072969 + 3 ^ 40 * 2382696 * 2
def baseEnd_2382696 : Nat := 90627281595949253677199

theorem tailTrace_2382696 : CollatzResearch.WordTrace tailWord_2382696 prefixEnd_2382696 90627281595949253677199 := by
  unfold tailWord_2382696
  simp only [CollatzResearch.WordTrace]
  refine ⟨43452031287953399462195971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57936041717271199282927961 43452031287953399462195971)
  ·
    refine ⟨65178046931930099193293957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43452031287953399462195971 65178046931930099193293957)
    ·
      refine ⟨12220883799736893598742617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65178046931930099193293957 12220883799736893598742617)
      ·
        refine ⟨9165662849802670199056963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12220883799736893598742617 9165662849802670199056963)
        ·
          refine ⟨13748494274704005298585445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9165662849802670199056963 13748494274704005298585445)
          ·
            refine ⟨2577842676507000993484771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13748494274704005298585445 2577842676507000993484771)
            ·
              refine ⟨3866764014760501490227157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2577842676507000993484771 3866764014760501490227157)
              ·
                refine ⟨90627281595949253677199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3866764014760501490227157 90627281595949253677199)
                ·
                  rfl

theorem cell22_2382696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 7].length) (baseStart_2382696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382696 prefixEnd_2382696 := by exact prefixLift 2382696
  have htrace : WordTrace (prefixWord ++ tailWord_2382696) baseStart_2382696 baseEnd_2382696 := by
    simpa [prefixWord, tailWord_2382696, baseEnd_2382696] using wordTrace_append hprefix tailTrace_2382696
  have hstable : (prefixWord ++ tailWord_2382696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382696).length < 2 ^ (prefixWord ++ tailWord_2382696).sum := by decide
  have hdescent : baseEnd_2382696 < baseStart_2382696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382724 : List Nat := [2, 3, 2, 1, 1, 1, 1, 4, 7]
def baseStart_2382724 : Nat := 118140960795 + 2382724 * 2 ^ 59
def prefixEnd_2382724 : Nat := 4983230072969 + 3 ^ 40 * 2382724 * 2
def baseEnd_2382724 : Nat := 271885039778586847798235

theorem tailTrace_2382724 : CollatzResearch.WordTrace tailWord_2382724 prefixEnd_2382724 271885039778586847798235 := by
  unfold tailWord_2382724
  simp only [CollatzResearch.WordTrace]
  refine ⟨43452541909902679853205613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57936722546536906470940817 43452541909902679853205613)
  ·
    refine ⟨16294703216213504944952105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43452541909902679853205613 16294703216213504944952105)
    ·
      refine ⟨12221027412160128708714079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16294703216213504944952105 12221027412160128708714079)
      ·
        refine ⟨18331541118240193063071119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12221027412160128708714079 18331541118240193063071119)
        ·
          refine ⟨27497311677360289594606679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18331541118240193063071119 27497311677360289594606679)
          ·
            refine ⟨41245967516040434391910019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27497311677360289594606679 41245967516040434391910019)
            ·
              refine ⟨61868951274060651587865029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41245967516040434391910019 61868951274060651587865029)
              ·
                refine ⟨11600428363886372172724693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61868951274060651587865029 11600428363886372172724693)
                ·
                  refine ⟨271885039778586847798235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11600428363886372172724693 271885039778586847798235)
                  ·
                    rfl

theorem cell22_2382724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_2382724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382724 prefixEnd_2382724 := by exact prefixLift 2382724
  have htrace : WordTrace (prefixWord ++ tailWord_2382724) baseStart_2382724 baseEnd_2382724 := by
    simpa [prefixWord, tailWord_2382724, baseEnd_2382724] using wordTrace_append hprefix tailTrace_2382724
  have hstable : (prefixWord ++ tailWord_2382724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382724).length < 2 ^ (prefixWord ++ tailWord_2382724).sum := by decide
  have hdescent : baseEnd_2382724 < baseStart_2382724 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382741 : List Nat := [1, 3, 2, 1, 1, 4, 3, 2, 5]
def baseStart_2382741 : Nat := 118140960795 + 2382741 * 2 ^ 59
def prefixEnd_2382741 : Nat := 4983230072969 + 3 ^ 40 * 2382741 * 2
def baseEnd_2382741 : Nat := 271886979594392721906551

theorem tailTrace_2382741 : CollatzResearch.WordTrace tailWord_2382741 prefixEnd_2382741 271886979594392721906551 := by
  unfold tailWord_2382741
  simp only [CollatzResearch.WordTrace]
  refine ⟨86905703860743771609780077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57937135907162514406520051 86905703860743771609780077)
  ·
    refine ⟨32589638947778914353667529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86905703860743771609780077 32589638947778914353667529)
    ·
      refine ⟨24442229210834185765250647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32589638947778914353667529 24442229210834185765250647)
      ·
        refine ⟨36663343816251278647875971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24442229210834185765250647 36663343816251278647875971)
        ·
          refine ⟨54995015724376917971813957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36663343816251278647875971 54995015724376917971813957)
          ·
            refine ⟨10311565448320672119715117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 54995015724376917971813957 10311565448320672119715117)
            ·
              refine ⟨3866837043120252044893169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10311565448320672119715117 3866837043120252044893169)
              ·
                refine ⟨2900127782340189033669877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3866837043120252044893169 2900127782340189033669877)
                ·
                  refine ⟨271886979594392721906551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2900127782340189033669877 271886979594392721906551)
                  ·
                    rfl

theorem cell22_2382741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 3, 2, 5].length) (baseStart_2382741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382741 prefixEnd_2382741 := by exact prefixLift 2382741
  have htrace : WordTrace (prefixWord ++ tailWord_2382741) baseStart_2382741 baseEnd_2382741 := by
    simpa [prefixWord, tailWord_2382741, baseEnd_2382741] using wordTrace_append hprefix tailTrace_2382741
  have hstable : (prefixWord ++ tailWord_2382741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382741).length < 2 ^ (prefixWord ++ tailWord_2382741).sum := by decide
  have hdescent : baseEnd_2382741 < baseStart_2382741 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382801 : List Nat := [1, 2, 2, 1, 2, 1, 3, 3, 4, 3]
def baseStart_2382801 : Nat := 118140960795 + 2382801 * 2 ^ 59
def prefixEnd_2382801 : Nat := 4983230072969 + 3 ^ 40 * 2382801 * 2
def baseEnd_2382801 : Nat := 815681478009358009219469

theorem tailTrace_2382801 : CollatzResearch.WordTrace tailWord_2382801 prefixEnd_2382801 815681478009358009219469 := by
  unfold tailWord_2382801
  simp only [CollatzResearch.WordTrace]
  refine ⟨86907892240526401856964257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57938594827017601237976171 86907892240526401856964257)
  ·
    refine ⟨65180919180394801392723193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86907892240526401856964257 65180919180394801392723193)
    ·
      refine ⟨48885689385296101044542395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65180919180394801392723193 48885689385296101044542395)
      ·
        refine ⟨73328534077944151566813593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48885689385296101044542395 73328534077944151566813593)
        ·
          refine ⟨54996400558458113675110195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73328534077944151566813593 54996400558458113675110195)
          ·
            refine ⟨82494600837687170512665293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 54996400558458113675110195 82494600837687170512665293)
            ·
              refine ⟨30935475314132688942249485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82494600837687170512665293 30935475314132688942249485)
              ·
                refine ⟨11600803242799758353343557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30935475314132688942249485 11600803242799758353343557)
                ·
                  refine ⟨2175150608024954691251917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11600803242799758353343557 2175150608024954691251917)
                  ·
                    refine ⟨815681478009358009219469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2175150608024954691251917 815681478009358009219469)
                    ·
                      rfl

theorem cell22_2382801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 3, 4, 3].length) (baseStart_2382801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382801 prefixEnd_2382801 := by exact prefixLift 2382801
  have htrace : WordTrace (prefixWord ++ tailWord_2382801) baseStart_2382801 baseEnd_2382801 := by
    simpa [prefixWord, tailWord_2382801, baseEnd_2382801] using wordTrace_append hprefix tailTrace_2382801
  have hstable : (prefixWord ++ tailWord_2382801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382801).length < 2 ^ (prefixWord ++ tailWord_2382801).sum := by decide
  have hdescent : baseEnd_2382801 < baseStart_2382801 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382833 : List Nat := [1, 2, 2, 2, 4, 2, 2, 1, 2, 4]
def baseStart_2382833 : Nat := 118140960795 + 2382833 * 2 ^ 59
def prefixEnd_2382833 : Nat := 4983230072969 + 3 ^ 40 * 2382833 * 2
def baseEnd_2382833 : Nat := 815692432263320592419371

theorem tailTrace_2382833 : CollatzResearch.WordTrace tailWord_2382833 prefixEnd_2382833 815692432263320592419371 := by
  unfold tailWord_2382833
  simp only [CollatzResearch.WordTrace]
  refine ⟨86909059376410471322129153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57939372917606980881419435 86909059376410471322129153)
  ·
    refine ⟨65181794532307853491596865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86909059376410471322129153 65181794532307853491596865)
    ·
      refine ⟨48886345899230890118697649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65181794532307853491596865 48886345899230890118697649)
      ·
        refine ⟨36664759424423167589023237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48886345899230890118697649 36664759424423167589023237)
        ·
          refine ⟨6874642392079343922941857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36664759424423167589023237 6874642392079343922941857)
          ·
            refine ⟨5155981794059507942206393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6874642392079343922941857 5155981794059507942206393)
            ·
              refine ⟨3866986345544630956654795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5155981794059507942206393 3866986345544630956654795)
              ·
                refine ⟨5800479518316946434982193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3866986345544630956654795 5800479518316946434982193)
                ·
                  refine ⟨4350359638737709826236645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5800479518316946434982193 4350359638737709826236645)
                  ·
                    refine ⟨815692432263320592419371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4350359638737709826236645 815692432263320592419371)
                    ·
                      rfl

theorem cell22_2382833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 2, 1, 2, 4].length) (baseStart_2382833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382833 prefixEnd_2382833 := by exact prefixLift 2382833
  have htrace : WordTrace (prefixWord ++ tailWord_2382833) baseStart_2382833 baseEnd_2382833 := by
    simpa [prefixWord, tailWord_2382833, baseEnd_2382833] using wordTrace_append hprefix tailTrace_2382833
  have hstable : (prefixWord ++ tailWord_2382833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382833).length < 2 ^ (prefixWord ++ tailWord_2382833).sum := by decide
  have hdescent : baseEnd_2382833 < baseStart_2382833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382910 : List Nat := [4, 2, 1, 3, 1, 1, 3, 2, 5]
def baseStart_2382910 : Nat := 118140960795 + 2382910 * 2 ^ 59
def prefixEnd_2382910 : Nat := 4983230072969 + 3 ^ 40 * 2382910 * 2
def baseEnd_2382910 : Nat := 271906263645639352748045

theorem tailTrace_2382910 : CollatzResearch.WordTrace tailWord_2382910 prefixEnd_2382910 271906263645639352748045 := by
  unfold tailWord_2382910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10863983474641439184085273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57941245198087675648454789 10863983474641439184085273)
  ·
    refine ⟨8147987605981079388063955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10863983474641439184085273 8147987605981079388063955)
    ·
      refine ⟨12221981408971619082095933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8147987605981079388063955 12221981408971619082095933)
      ·
        refine ⟨4583243028364357155785975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12221981408971619082095933 4583243028364357155785975)
        ·
          refine ⟨6874864542546535733678963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4583243028364357155785975 6874864542546535733678963)
          ·
            refine ⟨10312296813819803600518445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6874864542546535733678963 10312296813819803600518445)
            ·
              refine ⟨3867111305182426350194417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10312296813819803600518445 3867111305182426350194417)
              ·
                refine ⟨2900333478886819762645813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3867111305182426350194417 2900333478886819762645813)
                ·
                  refine ⟨271906263645639352748045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2900333478886819762645813 271906263645639352748045)
                  ·
                    rfl

theorem cell22_2382910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_2382910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382910 prefixEnd_2382910 := by exact prefixLift 2382910
  have htrace : WordTrace (prefixWord ++ tailWord_2382910) baseStart_2382910 baseEnd_2382910 := by
    simpa [prefixWord, tailWord_2382910, baseEnd_2382910] using wordTrace_append hprefix tailTrace_2382910
  have hstable : (prefixWord ++ tailWord_2382910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382910).length < 2 ^ (prefixWord ++ tailWord_2382910).sum := by decide
  have hdescent : baseEnd_2382910 < baseStart_2382910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382940 : List Nat := [2, 2, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_2382940 : Nat := 118140960795 + 2382940 * 2 ^ 59
def prefixEnd_2382940 : Nat := 4983230072969 + 3 ^ 40 * 2382940 * 2
def baseEnd_2382940 : Nat := 815729060550007979994043

theorem tailTrace_2382940 : CollatzResearch.WordTrace tailWord_2382940 prefixEnd_2382940 815729060550007979994043 := by
  unfold tailWord_2382940
  simp only [CollatzResearch.WordTrace]
  refine ⟨43456480993511414298137137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57941974658015219064182849 43456480993511414298137137)
  ·
    refine ⟨32592360745133560723602853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43456480993511414298137137 32592360745133560723602853)
    ·
      refine ⟨6111067639712542635675535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32592360745133560723602853 6111067639712542635675535)
      ·
        refine ⟨9166601459568813953513303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6111067639712542635675535 9166601459568813953513303)
        ·
          refine ⟨13749902189353220930269955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9166601459568813953513303 13749902189353220930269955)
          ·
            refine ⟨20624853284029831395404933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13749902189353220930269955 20624853284029831395404933)
            ·
              refine ⟨3867159990755593386638425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20624853284029831395404933 3867159990755593386638425)
              ·
                refine ⟨2900369993066695039978819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3867159990755593386638425 2900369993066695039978819)
                ·
                  refine ⟨4350554989600042559968229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2900369993066695039978819 4350554989600042559968229)
                  ·
                    refine ⟨815729060550007979994043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4350554989600042559968229 815729060550007979994043)
                    ·
                      rfl

theorem cell22_2382940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_2382940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382940 prefixEnd_2382940 := by exact prefixLift 2382940
  have htrace : WordTrace (prefixWord ++ tailWord_2382940) baseStart_2382940 baseEnd_2382940 := by
    simpa [prefixWord, tailWord_2382940, baseEnd_2382940] using wordTrace_append hprefix tailTrace_2382940
  have hstable : (prefixWord ++ tailWord_2382940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382940).length < 2 ^ (prefixWord ++ tailWord_2382940).sum := by decide
  have hdescent : baseEnd_2382940 < baseStart_2382940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2382953 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 4, 3]
def baseStart_2382953 : Nat := 118140960795 + 2382953 * 2 ^ 59
def prefixEnd_2382953 : Nat := 4983230072969 + 3 ^ 40 * 2382953 * 2
def baseEnd_2382953 : Nat := 815733510715680279419003

theorem tailTrace_2382953 : CollatzResearch.WordTrace tailWord_2382953 prefixEnd_2382953 815733510715680279419003 := by
  unfold tailWord_2382953
  simp only [CollatzResearch.WordTrace]
  refine ⟨86913436135975731816497513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57942290757317154544331675 86913436135975731816497513)
  ·
    refine ⟨65185077101981798862373135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86913436135975731816497513 65185077101981798862373135)
    ·
      refine ⟨97777615652972698293559703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65185077101981798862373135 97777615652972698293559703)
      ·
        refine ⟨146666423479459047440339555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97777615652972698293559703 146666423479459047440339555)
        ·
          refine ⟨219999635219188571160509333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146666423479459047440339555 219999635219188571160509333)
          ·
            refine ⟨10312482900899464273148875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 219999635219188571160509333 10312482900899464273148875)
            ·
              refine ⟨15468724351349196409723313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10312482900899464273148875 15468724351349196409723313)
              ·
                refine ⟨11601543263511897307292485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15468724351349196409723313 11601543263511897307292485)
                ·
                  refine ⟨2175289361908480745117341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11601543263511897307292485 2175289361908480745117341)
                  ·
                    refine ⟨815733510715680279419003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2175289361908480745117341 815733510715680279419003)
                    ·
                      rfl

theorem cell22_2382953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 4, 3].length) (baseStart_2382953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2382953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2382953 prefixEnd_2382953 := by exact prefixLift 2382953
  have htrace : WordTrace (prefixWord ++ tailWord_2382953) baseStart_2382953 baseEnd_2382953 := by
    simpa [prefixWord, tailWord_2382953, baseEnd_2382953] using wordTrace_append hprefix tailTrace_2382953
  have hstable : (prefixWord ++ tailWord_2382953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2382953).length < 2 ^ (prefixWord ++ tailWord_2382953).sum := by decide
  have hdescent : baseEnd_2382953 < baseStart_2382953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2382953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383011 : List Nat := [1, 1, 1, 4, 1, 1, 1, 3, 9]
def baseStart_2383011 : Nat := 118140960795 + 2383011 * 2 ^ 59
def prefixEnd_2383011 : Nat := 4983230072969 + 3 ^ 40 * 2383011 * 2
def baseEnd_2383011 : Nat := 271917788433662487156275

theorem tailTrace_2383011 : CollatzResearch.WordTrace tailWord_2383011 prefixEnd_2383011 271917788433662487156275 := by
  unfold tailWord_2383011
  simp only [CollatzResearch.WordTrace]
  refine ⟨86915551569765607722108887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57943701046510405148072591 86915551569765607722108887)
  ·
    refine ⟨130373327354648411583163331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86915551569765607722108887 130373327354648411583163331)
    ·
      refine ⟨195559991031972617374744997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130373327354648411583163331 195559991031972617374744997)
      ·
        refine ⟨36667498318494865757764687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 195559991031972617374744997 36667498318494865757764687)
        ·
          refine ⟨55001247477742298636647031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36667498318494865757764687 55001247477742298636647031)
          ·
            refine ⟨82501871216613447954970547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55001247477742298636647031 82501871216613447954970547)
            ·
              refine ⟨123752806824920171932455821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82501871216613447954970547 123752806824920171932455821)
              ·
                refine ⟨46407302559345064474670933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 123752806824920171932455821 46407302559345064474670933)
                ·
                  refine ⟨271917788433662487156275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46407302559345064474670933 271917788433662487156275)
                  ·
                    rfl

theorem cell22_2383011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 3, 9].length) (baseStart_2383011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383011 prefixEnd_2383011 := by exact prefixLift 2383011
  have htrace : WordTrace (prefixWord ++ tailWord_2383011) baseStart_2383011 baseEnd_2383011 := by
    simpa [prefixWord, tailWord_2383011, baseEnd_2383011] using wordTrace_append hprefix tailTrace_2383011
  have hstable : (prefixWord ++ tailWord_2383011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383011).length < 2 ^ (prefixWord ++ tailWord_2383011).sum := by decide
  have hdescent : baseEnd_2383011 < baseStart_2383011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383079 : List Nat := [1, 1, 5, 3, 3, 1, 1, 2, 5]
def baseStart_2383079 : Nat := 118140960795 + 2383079 * 2 ^ 59
def prefixEnd_2383079 : Nat := 4983230072969 + 3 ^ 40 * 2383079 * 2
def baseEnd_2383079 : Nat := 271925547696885983589539

theorem tailTrace_2383079 : CollatzResearch.WordTrace tailWord_2383079 prefixEnd_2383079 271925547696885983589539 := by
  unfold tailWord_2383079
  simp only [CollatzResearch.WordTrace]
  refine ⟨86918031733519255335584291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57945354489012836890389527 86918031733519255335584291)
  ·
    refine ⟨130377047600278883003376437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86918031733519255335584291 130377047600278883003376437)
    ·
      refine ⟨12222848212526145281566541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130377047600278883003376437 12222848212526145281566541)
      ·
        refine ⟨4583568079697304480587453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12222848212526145281566541 4583568079697304480587453)
        ·
          refine ⟨1718838029886489180220295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4583568079697304480587453 1718838029886489180220295)
          ·
            refine ⟨2578257044829733770330443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1718838029886489180220295 2578257044829733770330443)
            ·
              refine ⟨3867385567244600655495665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2578257044829733770330443 3867385567244600655495665)
              ·
                refine ⟨2900539175433450491621749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3867385567244600655495665 2900539175433450491621749)
                ·
                  refine ⟨271925547696885983589539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2900539175433450491621749 271925547696885983589539)
                  ·
                    rfl

theorem cell22_2383079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 2, 5].length) (baseStart_2383079 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383079 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383079 prefixEnd_2383079 := by exact prefixLift 2383079
  have htrace : WordTrace (prefixWord ++ tailWord_2383079) baseStart_2383079 baseEnd_2383079 := by
    simpa [prefixWord, tailWord_2383079, baseEnd_2383079] using wordTrace_append hprefix tailTrace_2383079
  have hstable : (prefixWord ++ tailWord_2383079).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383079).length < 2 ^ (prefixWord ++ tailWord_2383079).sum := by decide
  have hdescent : baseEnd_2383079 < baseStart_2383079 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383103 : List Nat := [1, 1, 2, 2, 1, 5, 1, 2, 1, 6]
def baseStart_2383103 : Nat := 118140960795 + 2383103 * 2 ^ 59
def prefixEnd_2383103 : Nat := 4983230072969 + 3 ^ 40 * 2383103 * 2
def baseEnd_2383103 : Nat := 815784858781129888168543

theorem tailTrace_2383103 : CollatzResearch.WordTrace tailWord_2383103 prefixEnd_2383103 815784858781129888168543 := by
  unfold tailWord_2383103
  simp only [CollatzResearch.WordTrace]
  refine ⟨86918907085432307434457963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57945938056954871622971975 86918907085432307434457963)
  ·
    refine ⟨130378360628148461151686945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86918907085432307434457963 130378360628148461151686945)
    ·
      refine ⟨97783770471111345863765209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130378360628148461151686945 97783770471111345863765209)
      ·
        refine ⟨73337827853333509397823907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97783770471111345863765209 73337827853333509397823907)
        ·
          refine ⟨110006741780000264096735861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73337827853333509397823907 110006741780000264096735861)
          ·
            refine ⟨10313132041875024759068987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110006741780000264096735861 10313132041875024759068987)
            ·
              refine ⟨15469698062812537138603481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10313132041875024759068987 15469698062812537138603481)
              ·
                refine ⟨11602273547109402853952611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15469698062812537138603481 11602273547109402853952611)
                ·
                  refine ⟨17403410320664104280928917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11602273547109402853952611 17403410320664104280928917)
                  ·
                    refine ⟨815784858781129888168543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17403410320664104280928917 815784858781129888168543)
                    ·
                      rfl

theorem cell22_2383103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_2383103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383103 prefixEnd_2383103 := by exact prefixLift 2383103
  have htrace : WordTrace (prefixWord ++ tailWord_2383103) baseStart_2383103 baseEnd_2383103 := by
    simpa [prefixWord, tailWord_2383103, baseEnd_2383103] using wordTrace_append hprefix tailTrace_2383103
  have hstable : (prefixWord ++ tailWord_2383103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383103).length < 2 ^ (prefixWord ++ tailWord_2383103).sum := by decide
  have hdescent : baseEnd_2383103 < baseStart_2383103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383105 : List Nat := [1, 2, 4, 1, 1, 3, 3, 1, 1, 5]
def baseStart_2383105 : Nat := 118140960795 + 2383105 * 2 ^ 59
def prefixEnd_2383105 : Nat := 4983230072969 + 3 ^ 40 * 2383105 * 2
def baseEnd_2383105 : Nat := 815785543422002549618537

theorem tailTrace_2383105 : CollatzResearch.WordTrace tailWord_2383105 prefixEnd_2383105 815785543422002549618537 := by
  unfold tailWord_2383105
  simp only [CollatzResearch.WordTrace]
  refine ⟨86918980031425061776030769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57945986687616707850687179 86918980031425061776030769)
  ·
    refine ⟨65189235023568796332023077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86918980031425061776030769 65189235023568796332023077)
    ·
      refine ⟨12222981566919149312254327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65189235023568796332023077 12222981566919149312254327)
      ·
        refine ⟨18334472350378723968381491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12222981566919149312254327 18334472350378723968381491)
        ·
          refine ⟨27501708525568085952572237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18334472350378723968381491 27501708525568085952572237)
          ·
            refine ⟨10313140697088032232214589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27501708525568085952572237 10313140697088032232214589)
            ·
              refine ⟨3867427761408012087080471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10313140697088032232214589 3867427761408012087080471)
              ·
                refine ⟨5801141642112018130620707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3867427761408012087080471 5801141642112018130620707)
                ·
                  refine ⟨8701712463168027195931061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5801141642112018130620707 8701712463168027195931061)
                  ·
                    refine ⟨815785543422002549618537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8701712463168027195931061 815785543422002549618537)
                    ·
                      rfl

theorem cell22_2383105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_2383105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383105 prefixEnd_2383105 := by exact prefixLift 2383105
  have htrace : WordTrace (prefixWord ++ tailWord_2383105) baseStart_2383105 baseEnd_2383105 := by
    simpa [prefixWord, tailWord_2383105, baseEnd_2383105] using wordTrace_append hprefix tailTrace_2383105
  have hstable : (prefixWord ++ tailWord_2383105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383105).length < 2 ^ (prefixWord ++ tailWord_2383105).sum := by decide
  have hdescent : baseEnd_2383105 < baseStart_2383105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383135 : List Nat := [1, 1, 2, 4, 4, 2, 8]
def baseStart_2383135 : Nat := 118140960795 + 2383135 * 2 ^ 59
def prefixEnd_2383135 : Nat := 4983230072969 + 3 ^ 40 * 2383135 * 2
def baseEnd_2383135 : Nat := 30214659742040461902535

theorem tailTrace_2383135 : CollatzResearch.WordTrace tailWord_2383135 prefixEnd_2383135 30214659742040461902535 := by
  unfold tailWord_2383135
  simp only [CollatzResearch.WordTrace]
  refine ⟨86920074221316376899622859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57946716147544251266415239 86920074221316376899622859)
  ·
    refine ⟨130380111331974565349434289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86920074221316376899622859 130380111331974565349434289)
    ·
      refine ⟨97785083498980924012075717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130380111331974565349434289 97785083498980924012075717)
      ·
        refine ⟨18334703156058923252264197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97785083498980924012075717 18334703156058923252264197)
        ·
          refine ⟨3437756841761048109799537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18334703156058923252264197 3437756841761048109799537)
          ·
            refine ⟨2578317631320786082349653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3437756841761048109799537 2578317631320786082349653)
            ·
              refine ⟨30214659742040461902535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2578317631320786082349653 30214659742040461902535)
              ·
                rfl

theorem cell22_2383135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 8].length) (baseStart_2383135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383135 prefixEnd_2383135 := by exact prefixLift 2383135
  have htrace : WordTrace (prefixWord ++ tailWord_2383135) baseStart_2383135 baseEnd_2383135 := by
    simpa [prefixWord, tailWord_2383135, baseEnd_2383135] using wordTrace_append hprefix tailTrace_2383135
  have hstable : (prefixWord ++ tailWord_2383135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383135).length < 2 ^ (prefixWord ++ tailWord_2383135).sum := by decide
  have hdescent : baseEnd_2383135 < baseStart_2383135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383148 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 2, 6]
def baseStart_2383148 : Nat := 118140960795 + 2383148 * 2 ^ 59
def prefixEnd_2383148 : Nat := 4983230072969 + 3 ^ 40 * 2383148 * 2
def baseEnd_2383148 : Nat := 815800263200764770793405

theorem tailTrace_2383148 : CollatzResearch.WordTrace tailWord_2383148 prefixEnd_2383148 815800263200764770793405 := by
  unfold tailWord_2383148
  simp only [CollatzResearch.WordTrace]
  refine ⟨43460274185134640059923049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57947032246846186746564065 43460274185134640059923049)
  ·
    refine ⟨32595205638850980044942287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43460274185134640059923049 32595205638850980044942287)
    ·
      refine ⟨48892808458276470067413431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32595205638850980044942287 48892808458276470067413431)
      ·
        refine ⟨73339212687414705101120147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48892808458276470067413431 73339212687414705101120147)
        ·
          refine ⟨110008819031122057651680221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73339212687414705101120147 110008819031122057651680221)
          ·
            refine ⟨41253307136670771619380083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110008819031122057651680221 41253307136670771619380083)
            ·
              refine ⟨61879960705006157429070125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41253307136670771619380083 61879960705006157429070125)
              ·
                refine ⟨23204985264377309035901297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61879960705006157429070125 23204985264377309035901297)
                ·
                  refine ⟨17403738948282981776925973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23204985264377309035901297 17403738948282981776925973)
                  ·
                    refine ⟨815800263200764770793405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17403738948282981776925973 815800263200764770793405)
                    ·
                      rfl

theorem cell22_2383148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 6].length) (baseStart_2383148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383148 prefixEnd_2383148 := by exact prefixLift 2383148
  have htrace : WordTrace (prefixWord ++ tailWord_2383148) baseStart_2383148 baseEnd_2383148 := by
    simpa [prefixWord, tailWord_2383148, baseEnd_2383148] using wordTrace_append hprefix tailTrace_2383148
  have hstable : (prefixWord ++ tailWord_2383148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383148).length < 2 ^ (prefixWord ++ tailWord_2383148).sum := by decide
  have hdescent : baseEnd_2383148 < baseStart_2383148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383190 : List Nat := [5, 2, 3, 1, 1, 1, 2, 2, 2, 3]
def baseStart_2383190 : Nat := 118140960795 + 2383190 * 2 ^ 59
def prefixEnd_2383190 : Nat := 4983230072969 + 3 ^ 40 * 2383190 * 2
def baseEnd_2383190 : Nat := 815814640659090661243277

theorem tailTrace_2383190 : CollatzResearch.WordTrace tailWord_2383190 prefixEnd_2383190 815814640659090661243277 := by
  unfold tailWord_2383190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5432630014757320080804689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57948053490744747528583349 5432630014757320080804689)
  ·
    refine ⟨4074472511067990060603517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5432630014757320080804689 4074472511067990060603517)
    ·
      refine ⟨1527927191650496272726319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4074472511067990060603517 1527927191650496272726319)
      ·
        refine ⟨2291890787475744409089479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1527927191650496272726319 2291890787475744409089479)
        ·
          refine ⟨3437836181213616613634219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2291890787475744409089479 3437836181213616613634219)
          ·
            refine ⟨5156754271820424920451329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3437836181213616613634219 5156754271820424920451329)
            ·
              refine ⟨3867565703865318690338497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5156754271820424920451329 3867565703865318690338497)
              ·
                refine ⟨2900674277898989017753873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3867565703865318690338497 2900674277898989017753873)
                ·
                  refine ⟨2175505708424241763315405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2900674277898989017753873 2175505708424241763315405)
                  ·
                    refine ⟨815814640659090661243277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2175505708424241763315405 815814640659090661243277)
                    ·
                      rfl

theorem cell22_2383190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_2383190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383190 prefixEnd_2383190 := by exact prefixLift 2383190
  have htrace : WordTrace (prefixWord ++ tailWord_2383190) baseStart_2383190 baseEnd_2383190 := by
    simpa [prefixWord, tailWord_2383190, baseEnd_2383190] using wordTrace_append hprefix tailTrace_2383190
  have hstable : (prefixWord ++ tailWord_2383190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383190).length < 2 ^ (prefixWord ++ tailWord_2383190).sum := by decide
  have hdescent : baseEnd_2383190 < baseStart_2383190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383255 : List Nat := [1, 1, 3, 3, 1, 1, 1, 3, 4, 4]
def baseStart_2383255 : Nat := 118140960795 + 2383255 * 2 ^ 59
def prefixEnd_2383255 : Nat := 4983230072969 + 3 ^ 40 * 2383255 * 2
def baseEnd_2383255 : Nat := 815836891487452158368077

theorem tailTrace_2383255 : CollatzResearch.WordTrace tailWord_2383255 prefixEnd_2383255 815836891487452158368077 := by
  unfold tailWord_2383255
  simp only [CollatzResearch.WordTrace]
  refine ⟨86924450980881637393991219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57949633987254424929327479 86924450980881637393991219)
  ·
    refine ⟨130386676471322456090986829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86924450980881637393991219 130386676471322456090986829)
    ·
      refine ⟨48895003676745921034120061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130386676471322456090986829 48895003676745921034120061)
      ·
        refine ⟨18335626378779720387795023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48895003676745921034120061 18335626378779720387795023)
        ·
          refine ⟨27503439568169580581692535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18335626378779720387795023 27503439568169580581692535)
          ·
            refine ⟨41255159352254370872538803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27503439568169580581692535 41255159352254370872538803)
            ·
              refine ⟨61882739028381556308808205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41255159352254370872538803 61882739028381556308808205)
              ·
                refine ⟨23206027135643083615803077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61882739028381556308808205 23206027135643083615803077)
                ·
                  refine ⟨4351130087933078177963077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23206027135643083615803077 4351130087933078177963077)
                  ·
                    refine ⟨815836891487452158368077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4351130087933078177963077 815836891487452158368077)
                    ·
                      rfl

theorem cell22_2383255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_2383255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383255 prefixEnd_2383255 := by exact prefixLift 2383255
  have htrace : WordTrace (prefixWord ++ tailWord_2383255) baseStart_2383255 baseEnd_2383255 := by
    simpa [prefixWord, tailWord_2383255, baseEnd_2383255] using wordTrace_append hprefix tailTrace_2383255
  have hstable : (prefixWord ++ tailWord_2383255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383255).length < 2 ^ (prefixWord ++ tailWord_2383255).sum := by decide
  have hdescent : baseEnd_2383255 < baseStart_2383255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383257 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 4, 3]
def baseStart_2383257 : Nat := 118140960795 + 2383257 * 2 ^ 59
def prefixEnd_2383257 : Nat := 4983230072969 + 3 ^ 40 * 2383257 * 2
def baseEnd_2383257 : Nat := 815837576128324819818071

theorem tailTrace_2383257 : CollatzResearch.WordTrace tailWord_2383257 prefixEnd_2383257 815837576128324819818071 := by
  unfold tailWord_2383257
  simp only [CollatzResearch.WordTrace]
  refine ⟨86924523926874391735564025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57949682617916261157042683 86924523926874391735564025)
  ·
    refine ⟨65193392945155793801673019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86924523926874391735564025 65193392945155793801673019)
    ·
      refine ⟨97790089417733690702509529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65193392945155793801673019 97790089417733690702509529)
      ·
        refine ⟨73342567063300268026882147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97790089417733690702509529 73342567063300268026882147)
        ·
          refine ⟨110013850594950402040323221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73342567063300268026882147 110013850594950402040323221)
          ·
            refine ⟨5156899246638300095640151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 110013850594950402040323221 5156899246638300095640151)
            ·
              refine ⟨7735348869957450143460227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5156899246638300095640151 7735348869957450143460227)
              ·
                refine ⟨11603023304936175215190341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7735348869957450143460227 11603023304936175215190341)
                ·
                  refine ⟨2175566869675532852848189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11603023304936175215190341 2175566869675532852848189)
                  ·
                    refine ⟨815837576128324819818071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2175566869675532852848189 815837576128324819818071)
                    ·
                      rfl

theorem cell22_2383257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 4, 3].length) (baseStart_2383257 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383257 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383257 prefixEnd_2383257 := by exact prefixLift 2383257
  have htrace : WordTrace (prefixWord ++ tailWord_2383257) baseStart_2383257 baseEnd_2383257 := by
    simpa [prefixWord, tailWord_2383257, baseEnd_2383257] using wordTrace_append hprefix tailTrace_2383257
  have hstable : (prefixWord ++ tailWord_2383257).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383257).length < 2 ^ (prefixWord ++ tailWord_2383257).sum := by decide
  have hdescent : baseEnd_2383257 < baseStart_2383257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383319 : List Nat := [1, 1, 3, 2, 1, 1, 1, 8, 1, 3]
def baseStart_2383319 : Nat := 118140960795 + 2383319 * 2 ^ 59
def prefixEnd_2383319 : Nat := 4983230072969 + 3 ^ 40 * 2383319 * 2
def baseEnd_2383319 : Nat := 815858799995377324767881

theorem tailTrace_2383319 : CollatzResearch.WordTrace tailWord_2383319 prefixEnd_2383319 815858799995377324767881 := by
  unfold tailWord_2383319
  simp only [CollatzResearch.WordTrace]
  refine ⟨86926785252649776324321011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57951190168433184216214007 86926785252649776324321011)
  ·
    refine ⟨130390177878974664486481517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86926785252649776324321011 130390177878974664486481517)
    ·
      refine ⟨48896316704615499182430569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130390177878974664486481517 48896316704615499182430569)
      ·
        refine ⟨36672237528461624386822927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48896316704615499182430569 36672237528461624386822927)
        ·
          refine ⟨55008356292692436580234391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36672237528461624386822927 55008356292692436580234391)
          ·
            refine ⟨82512534439038654870351587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55008356292692436580234391 82512534439038654870351587)
            ·
              refine ⟨123768801658557982305527381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82512534439038654870351587 123768801658557982305527381)
              ·
                refine ⟨1450415644436226355142899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 123768801658557982305527381 1450415644436226355142899)
                ·
                  refine ⟨2175623466654339532714349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450415644436226355142899 2175623466654339532714349)
                  ·
                    refine ⟨815858799995377324767881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2175623466654339532714349 815858799995377324767881)
                    ·
                      rfl

theorem cell22_2383319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 8, 1, 3].length) (baseStart_2383319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383319 prefixEnd_2383319 := by exact prefixLift 2383319
  have htrace : WordTrace (prefixWord ++ tailWord_2383319) baseStart_2383319 baseEnd_2383319 := by
    simpa [prefixWord, tailWord_2383319, baseEnd_2383319] using wordTrace_append hprefix tailTrace_2383319
  have hstable : (prefixWord ++ tailWord_2383319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383319).length < 2 ^ (prefixWord ++ tailWord_2383319).sum := by decide
  have hdescent : baseEnd_2383319 < baseStart_2383319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383482 : List Nat := [3, 1, 1, 1, 1, 1, 1, 6, 2, 5]
def baseStart_2383482 : Nat := 118140960795 + 2383482 * 2 ^ 59
def prefixEnd_2383482 : Nat := 4983230072969 + 3 ^ 40 * 2383482 * 2
def baseEnd_2383482 : Nat := 815914598226499232942381

theorem tailTrace_2383482 : CollatzResearch.WordTrace tailWord_2383482 prefixEnd_2383482 815914598226499232942381 := by
  unfold tailWord_2383482
  simp only [CollatzResearch.WordTrace]
  refine ⟨21733182587764813790626175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57955153567372836775003133 21733182587764813790626175)
  ·
    refine ⟨32599773881647220685939263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21733182587764813790626175 32599773881647220685939263)
    ·
      refine ⟨48899660822470831028908895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32599773881647220685939263 48899660822470831028908895)
      ·
        refine ⟨73349491233706246543363343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48899660822470831028908895 73349491233706246543363343)
        ·
          refine ⟨110024236850559369815045015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73349491233706246543363343 110024236850559369815045015)
          ·
            refine ⟨165036355275839054722567523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110024236850559369815045015 165036355275839054722567523)
            ·
              refine ⟨247554532913758582083851285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165036355275839054722567523 247554532913758582083851285)
              ·
                refine ⟨11604118730332433535180529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 247554532913758582083851285 11604118730332433535180529)
                ·
                  refine ⟨8703089047749325151385397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11604118730332433535180529 8703089047749325151385397)
                  ·
                    refine ⟨815914598226499232942381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8703089047749325151385397 815914598226499232942381)
                    ·
                      rfl

theorem cell22_2383482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_2383482 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383482 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383482 prefixEnd_2383482 := by exact prefixLift 2383482
  have htrace : WordTrace (prefixWord ++ tailWord_2383482) baseStart_2383482 baseEnd_2383482 := by
    simpa [prefixWord, tailWord_2383482, baseEnd_2383482] using wordTrace_append hprefix tailTrace_2383482
  have hstable : (prefixWord ++ tailWord_2383482).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383482).length < 2 ^ (prefixWord ++ tailWord_2383482).sum := by decide
  have hdescent : baseEnd_2383482 < baseStart_2383482 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383488 : List Nat := [2, 1, 1, 2, 1, 4, 5, 2, 1, 3]
def baseStart_2383488 : Nat := 118140960795 + 2383488 * 2 ^ 59
def prefixEnd_2383488 : Nat := 4983230072969 + 3 ^ 40 * 2383488 * 2
def baseEnd_2383488 : Nat := 815916652149117217292363

theorem tailTrace_2383488 : CollatzResearch.WordTrace tailWord_2383488 prefixEnd_2383488 815916652149117217292363 := by
  unfold tailWord_2383488
  simp only [CollatzResearch.WordTrace]
  refine ⟨43466474594518759093611559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57955299459358345458148745 43466474594518759093611559)
  ·
    refine ⟨65199711891778138640417339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43466474594518759093611559 65199711891778138640417339)
    ·
      refine ⟨97799567837667207960626009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65199711891778138640417339 97799567837667207960626009)
      ·
        refine ⟨73349675878250405970469507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97799567837667207960626009 73349675878250405970469507)
        ·
          refine ⟨110024513817375608955704261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73349675878250405970469507 110024513817375608955704261)
          ·
            refine ⟨20629596340757926679194549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 110024513817375608955704261 20629596340757926679194549)
            ·
              refine ⟨1934024656946055626174489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 20629596340757926679194549 1934024656946055626174489)
              ·
                refine ⟨1450518492709541719630867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1934024656946055626174489 1450518492709541719630867)
                ·
                  refine ⟨2175777739064312579446301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450518492709541719630867 2175777739064312579446301)
                  ·
                    refine ⟨815916652149117217292363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2175777739064312579446301 815916652149117217292363)
                    ·
                      rfl

theorem cell22_2383488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 5, 2, 1, 3].length) (baseStart_2383488 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383488 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383488 prefixEnd_2383488 := by exact prefixLift 2383488
  have htrace : WordTrace (prefixWord ++ tailWord_2383488) baseStart_2383488 baseEnd_2383488 := by
    simpa [prefixWord, tailWord_2383488, baseEnd_2383488] using wordTrace_append hprefix tailTrace_2383488
  have hstable : (prefixWord ++ tailWord_2383488).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383488).length < 2 ^ (prefixWord ++ tailWord_2383488).sum := by decide
  have hdescent : baseEnd_2383488 < baseStart_2383488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383544 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 4, 3]
def baseStart_2383544 : Nat := 118140960795 + 2383544 * 2 ^ 59
def prefixEnd_2383544 : Nat := 4983230072969 + 3 ^ 40 * 2383544 * 2
def baseEnd_2383544 : Nat := 815935822093551737892191

theorem tailTrace_2383544 : CollatzResearch.WordTrace tailWord_2383544 prefixEnd_2383544 815935822093551737892191 := by
  unfold tailWord_2383544
  simp only [CollatzResearch.WordTrace]
  refine ⟨43467495838417319875630843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57956661117889759834174457 43467495838417319875630843)
  ·
    refine ⟨65201243757625979813446265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43467495838417319875630843 65201243757625979813446265)
    ·
      refine ⟨48900932818219484860084699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65201243757625979813446265 48900932818219484860084699)
      ·
        refine ⟨73351399227329227290127049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48900932818219484860084699 73351399227329227290127049)
        ·
          refine ⟨55013549420496920467595287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73351399227329227290127049 55013549420496920467595287)
          ·
            refine ⟨82520324130745380701392931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55013549420496920467595287 82520324130745380701392931)
            ·
              refine ⟨123780486196118071052089397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82520324130745380701392931 123780486196118071052089397)
              ·
                refine ⟨11604420580886069161133381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123780486196118071052089397 11604420580886069161133381)
                ·
                  refine ⟨2175828858916137967712509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11604420580886069161133381 2175828858916137967712509)
                  ·
                    refine ⟨815935822093551737892191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2175828858916137967712509 815935822093551737892191)
                    ·
                      rfl

theorem cell22_2383544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 4, 3].length) (baseStart_2383544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383544 prefixEnd_2383544 := by exact prefixLift 2383544
  have htrace : WordTrace (prefixWord ++ tailWord_2383544) baseStart_2383544 baseEnd_2383544 := by
    simpa [prefixWord, tailWord_2383544, baseEnd_2383544] using wordTrace_append hprefix tailTrace_2383544
  have hstable : (prefixWord ++ tailWord_2383544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383544).length < 2 ^ (prefixWord ++ tailWord_2383544).sum := by decide
  have hdescent : baseEnd_2383544 < baseStart_2383544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383546 : List Nat := [3, 1, 1, 1, 2, 5, 1, 4, 4]
def baseStart_2383546 : Nat := 118140960795 + 2383546 * 2 ^ 59
def prefixEnd_2383546 : Nat := 4983230072969 + 3 ^ 40 * 2383546 * 2
def baseEnd_2383546 : Nat := 271978835578141466447395

theorem tailTrace_2383546 : CollatzResearch.WordTrace tailWord_2383546 prefixEnd_2383546 271978835578141466447395 := by
  unfold tailWord_2383546
  simp only [CollatzResearch.WordTrace]
  refine ⟨21733766155706848523208623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57956709748551596061889661 21733766155706848523208623)
  ·
    refine ⟨32600649233560272784812935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21733766155706848523208623 32600649233560272784812935)
    ·
      refine ⟨48900973850340409177219403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32600649233560272784812935 48900973850340409177219403)
      ·
        refine ⟨73351460775510613765829105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48900973850340409177219403 73351460775510613765829105)
        ·
          refine ⟨55013595581632960324371829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73351460775510613765829105 55013595581632960324371829)
          ·
            refine ⟨5157524585778090030409859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55013595581632960324371829 5157524585778090030409859)
            ·
              refine ⟨7736286878667135045614789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5157524585778090030409859 7736286878667135045614789)
              ·
                refine ⟨1450553789750087821052773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7736286878667135045614789 1450553789750087821052773)
                ·
                  refine ⟨271978835578141466447395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1450553789750087821052773 271978835578141466447395)
                  ·
                    rfl

theorem cell22_2383546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 4, 4].length) (baseStart_2383546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383546 prefixEnd_2383546 := by exact prefixLift 2383546
  have htrace : WordTrace (prefixWord ++ tailWord_2383546) baseStart_2383546 baseEnd_2383546 := by
    simpa [prefixWord, tailWord_2383546, baseEnd_2383546] using wordTrace_append hprefix tailTrace_2383546
  have hstable : (prefixWord ++ tailWord_2383546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383546).length < 2 ^ (prefixWord ++ tailWord_2383546).sum := by decide
  have hdescent : baseEnd_2383546 < baseStart_2383546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383580 : List Nat := [2, 2, 5, 1, 2, 1, 2, 3, 4]
def baseStart_2383580 : Nat := 118140960795 + 2383580 * 2 ^ 59
def prefixEnd_2383580 : Nat := 4983230072969 + 3 ^ 40 * 2383580 * 2
def baseEnd_2383580 : Nat := 271982715209753214664027

theorem tailTrace_2383580 : CollatzResearch.WordTrace tailWord_2383580 prefixEnd_2383580 271982715209753214664027 := by
  unfold tailWord_2383580
  simp only [CollatzResearch.WordTrace]
  refine ⟨43468152352352108949786097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57957536469802811933048129 43468152352352108949786097)
  ·
    refine ⟨32601114264264081712339573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43468152352352108949786097 32601114264264081712339573)
    ·
      refine ⟨3056354462274757660531835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 32601114264264081712339573 3056354462274757660531835)
      ·
        refine ⟨4584531693412136490797753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3056354462274757660531835 4584531693412136490797753)
        ·
          refine ⟨3438398770059102368098315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4584531693412136490797753 3438398770059102368098315)
          ·
            refine ⟨5157598155088653552147473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438398770059102368098315 5157598155088653552147473)
            ·
              refine ⟨3868198616316490164110605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5157598155088653552147473 3868198616316490164110605)
              ·
                refine ⟨1450574481118683811541477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3868198616316490164110605 1450574481118683811541477)
                ·
                  refine ⟨271982715209753214664027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1450574481118683811541477 271982715209753214664027)
                  ·
                    rfl

theorem cell22_2383580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 3, 4].length) (baseStart_2383580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383580 prefixEnd_2383580 := by exact prefixLift 2383580
  have htrace : WordTrace (prefixWord ++ tailWord_2383580) baseStart_2383580 baseEnd_2383580 := by
    simpa [prefixWord, tailWord_2383580, baseEnd_2383580] using wordTrace_append hprefix tailTrace_2383580
  have hstable : (prefixWord ++ tailWord_2383580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383580).length < 2 ^ (prefixWord ++ tailWord_2383580).sum := by decide
  have hdescent : baseEnd_2383580 < baseStart_2383580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383591 : List Nat := [1, 1, 5, 4, 1, 1, 9]
def baseStart_2383591 : Nat := 118140960795 + 2383591 * 2 ^ 59
def prefixEnd_2383591 : Nat := 4983230072969 + 3 ^ 40 * 2383591 * 2
def baseEnd_2383591 : Nat := 30220441153854047480261

theorem tailTrace_2383591 : CollatzResearch.WordTrace tailWord_2383591 prefixEnd_2383591 30220441153854047480261 := by
  unfold tailWord_2383591
  simp only [CollatzResearch.WordTrace]
  refine ⟨86936705907664366778222627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57957803938442911185481751 86936705907664366778222627)
  ·
    refine ⟨130405058861496550167333941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86936705907664366778222627 130405058861496550167333941)
    ·
      refine ⟨12225474268265301578187557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130405058861496550167333941 12225474268265301578187557)
      ·
        refine ⟨2292276425299744045910167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12225474268265301578187557 2292276425299744045910167)
        ·
          refine ⟨3438414637949616068865251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292276425299744045910167 3438414637949616068865251)
          ·
            refine ⟨5157621956924424103297877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438414637949616068865251 5157621956924424103297877)
            ·
              refine ⟨30220441153854047480261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5157621956924424103297877 30220441153854047480261)
              ·
                rfl

theorem cell22_2383591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 9].length) (baseStart_2383591 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383591 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383591 prefixEnd_2383591 := by exact prefixLift 2383591
  have htrace : WordTrace (prefixWord ++ tailWord_2383591) baseStart_2383591 baseEnd_2383591 := by
    simpa [prefixWord, tailWord_2383591, baseEnd_2383591] using wordTrace_append hprefix tailTrace_2383591
  have hstable : (prefixWord ++ tailWord_2383591).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383591).length < 2 ^ (prefixWord ++ tailWord_2383591).sum := by decide
  have hdescent : baseEnd_2383591 < baseStart_2383591 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383619 : List Nat := [1, 1, 1, 3, 2, 2, 2, 5, 5]
def baseStart_2383619 : Nat := 118140960795 + 2383619 * 2 ^ 59
def prefixEnd_2383619 : Nat := 4983230072969 + 3 ^ 40 * 2383619 * 2
def baseEnd_2383619 : Nat := 271987165375425514088987

theorem tailTrace_2383619 : CollatzResearch.WordTrace tailWord_2383619 prefixEnd_2383619 271987165375425514088987 := by
  unfold tailWord_2383619
  simp only [CollatzResearch.WordTrace]
  refine ⟨86937727151562927560241911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57958484767708618373494607 86937727151562927560241911)
  ·
    refine ⟨130406590727344391340362867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86937727151562927560241911 130406590727344391340362867)
    ·
      refine ⟨195609886091016587010544301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130406590727344391340362867 195609886091016587010544301)
      ·
        refine ⟨73353707284131220128954113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195609886091016587010544301 73353707284131220128954113)
        ·
          refine ⟨55015280463098415096715585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73353707284131220128954113 55015280463098415096715585)
          ·
            refine ⟨41261460347323811322536689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55015280463098415096715585 41261460347323811322536689)
            ·
              refine ⟨30946095260492858491902517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41261460347323811322536689 30946095260492858491902517)
              ·
                refine ⟨2901196430671205483615861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 30946095260492858491902517 2901196430671205483615861)
                ·
                  refine ⟨271987165375425514088987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2901196430671205483615861 271987165375425514088987)
                  ·
                    rfl

theorem cell22_2383619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 5, 5].length) (baseStart_2383619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383619 prefixEnd_2383619 := by exact prefixLift 2383619
  have htrace : WordTrace (prefixWord ++ tailWord_2383619) baseStart_2383619 baseEnd_2383619 := by
    simpa [prefixWord, tailWord_2383619, baseEnd_2383619] using wordTrace_append hprefix tailTrace_2383619
  have hstable : (prefixWord ++ tailWord_2383619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383619).length < 2 ^ (prefixWord ++ tailWord_2383619).sum := by decide
  have hdescent : baseEnd_2383619 < baseStart_2383619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383670 : List Nat := [5, 1, 2, 2, 1, 1, 4, 1, 5]
def baseStart_2383670 : Nat := 118140960795 + 2383670 * 2 ^ 59
def prefixEnd_2383670 : Nat := 4983230072969 + 3 ^ 40 * 2383670 * 2
def baseEnd_2383670 : Nat := 271992984822843136413935

theorem tailTrace_2383670 : CollatzResearch.WordTrace tailWord_2383670 prefixEnd_2383670 271992984822843136413935 := by
  unfold tailWord_2383670
  simp only [CollatzResearch.WordTrace]
  refine ⟨5433724204648635204396779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57959724849585442180232309 5433724204648635204396779)
  ·
    refine ⟨8150586306972952806595169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5433724204648635204396779 8150586306972952806595169)
    ·
      refine ⟨6112939730229714604946377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8150586306972952806595169 6112939730229714604946377)
      ·
        refine ⟨4584704797672285953709783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6112939730229714604946377 4584704797672285953709783)
        ·
          refine ⟨6877057196508428930564675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4584704797672285953709783 6877057196508428930564675)
          ·
            refine ⟨10315585794762643395847013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6877057196508428930564675 10315585794762643395847013)
            ·
              refine ⟨1934172336517995636721315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10315585794762643395847013 1934172336517995636721315)
              ·
                refine ⟨2901258504776993455081973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934172336517995636721315 2901258504776993455081973)
                ·
                  refine ⟨271992984822843136413935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2901258504776993455081973 271992984822843136413935)
                  ·
                    rfl

theorem cell22_2383670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 4, 1, 5].length) (baseStart_2383670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383670 prefixEnd_2383670 := by exact prefixLift 2383670
  have htrace : WordTrace (prefixWord ++ tailWord_2383670) baseStart_2383670 baseEnd_2383670 := by
    simpa [prefixWord, tailWord_2383670, baseEnd_2383670] using wordTrace_append hprefix tailTrace_2383670
  have hstable : (prefixWord ++ tailWord_2383670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383670).length < 2 ^ (prefixWord ++ tailWord_2383670).sum := by decide
  have hdescent : baseEnd_2383670 < baseStart_2383670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383683 : List Nat := [1, 1, 1, 3, 1, 7, 1, 2, 1, 4]
def baseStart_2383683 : Nat := 118140960795 + 2383683 * 2 ^ 59
def prefixEnd_2383683 : Nat := 4983230072969 + 3 ^ 40 * 2383683 * 2
def baseEnd_2383683 : Nat := 815983404634201708666765

theorem tailTrace_2383683 : CollatzResearch.WordTrace tailWord_2383683 prefixEnd_2383683 815983404634201708666765 := by
  unfold tailWord_2383683
  simp only [CollatzResearch.WordTrace]
  refine ⟨86940061423331066490571703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57960040948887377660381135 86940061423331066490571703)
  ·
    refine ⟨130410092134996599735857555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86940061423331066490571703 130410092134996599735857555)
    ·
      refine ⟨195615138202494899603786333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130410092134996599735857555 195615138202494899603786333)
      ·
        refine ⟨73355676825935587351419875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195615138202494899603786333 73355676825935587351419875)
        ·
          refine ⟨110033515238903381027129813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73355676825935587351419875 110033515238903381027129813)
          ·
            refine ⟨2578910513411797992823355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 110033515238903381027129813 2578910513411797992823355)
            ·
              refine ⟨3868365770117696989235033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2578910513411797992823355 3868365770117696989235033)
              ·
                refine ⟨2901274327588272741926275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3868365770117696989235033 2901274327588272741926275)
                ·
                  refine ⟨4351911491382409112889413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2901274327588272741926275 4351911491382409112889413)
                  ·
                    refine ⟨815983404634201708666765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4351911491382409112889413 815983404634201708666765)
                    ·
                      rfl

theorem cell22_2383683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 2, 1, 4].length) (baseStart_2383683 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383683 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383683 prefixEnd_2383683 := by exact prefixLift 2383683
  have htrace : WordTrace (prefixWord ++ tailWord_2383683) baseStart_2383683 baseEnd_2383683 := by
    simpa [prefixWord, tailWord_2383683, baseEnd_2383683] using wordTrace_append hprefix tailTrace_2383683
  have hstable : (prefixWord ++ tailWord_2383683).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383683).length < 2 ^ (prefixWord ++ tailWord_2383683).sum := by decide
  have hdescent : baseEnd_2383683 < baseStart_2383683 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383700 : List Nat := [2, 4, 1, 1, 3, 2, 3, 1, 1, 4]
def baseStart_2383700 : Nat := 118140960795 + 2383700 * 2 ^ 59
def prefixEnd_2383700 : Nat := 4983230072969 + 3 ^ 40 * 2383700 * 2
def baseEnd_2383700 : Nat := 815989224081619330991713

theorem tailTrace_2383700 : CollatzResearch.WordTrace tailWord_2383700 prefixEnd_2383700 815989224081619330991713 := by
  unfold tailWord_2383700
  simp only [CollatzResearch.WordTrace]
  refine ⟨43470340732134739196970277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57960454309512985595960369 43470340732134739196970277)
  ·
    refine ⟨8150688887275263599431927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43470340732134739196970277 8150688887275263599431927)
    ·
      refine ⟨12226033330912895399147891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8150688887275263599431927 12226033330912895399147891)
      ·
        refine ⟨18339049996369343098721837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12226033330912895399147891 18339049996369343098721837)
        ·
          refine ⟨6877143748638503662020689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18339049996369343098721837 6877143748638503662020689)
          ·
            refine ⟨5157857811478877746515517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6877143748638503662020689 5157857811478877746515517)
            ·
              refine ⟨1934196679304579154943319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5157857811478877746515517 1934196679304579154943319)
              ·
                refine ⟨2901295018956868732414979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934196679304579154943319 2901295018956868732414979)
                ·
                  refine ⟨4351942528435303098622469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2901295018956868732414979 4351942528435303098622469)
                  ·
                    refine ⟨815989224081619330991713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4351942528435303098622469 815989224081619330991713)
                    ·
                      rfl

theorem cell22_2383700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 2, 3, 1, 1, 4].length) (baseStart_2383700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383700 prefixEnd_2383700 := by exact prefixLift 2383700
  have htrace : WordTrace (prefixWord ++ tailWord_2383700) baseStart_2383700 baseEnd_2383700 := by
    simpa [prefixWord, tailWord_2383700, baseEnd_2383700] using wordTrace_append hprefix tailTrace_2383700
  have hstable : (prefixWord ++ tailWord_2383700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383700).length < 2 ^ (prefixWord ++ tailWord_2383700).sum := by decide
  have hdescent : baseEnd_2383700 < baseStart_2383700 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383711 : List Nat := [1, 1, 2, 3, 1, 4, 2, 2, 2, 4]
def baseStart_2383711 : Nat := 118140960795 + 2383711 * 2 ^ 59
def prefixEnd_2383711 : Nat := 4983230072969 + 3 ^ 40 * 2383711 * 2
def baseEnd_2383711 : Nat := 815992989606418968966679

theorem tailTrace_2383711 : CollatzResearch.WordTrace tailWord_2383711 prefixEnd_2383711 815992989606418968966679 := by
  unfold tailWord_2383711
  simp only [CollatzResearch.WordTrace]
  refine ⟨86941082667229627272590987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57960721778153084848393991 86941082667229627272590987)
  ·
    refine ⟨130411624000844440908886481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86941082667229627272590987 130411624000844440908886481)
    ·
      refine ⟨97808718000633330681664861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130411624000844440908886481 97808718000633330681664861)
      ·
        refine ⟨36678269250237499005624323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97808718000633330681664861 36678269250237499005624323)
        ·
          refine ⟨55017403875356248508436485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36678269250237499005624323 55017403875356248508436485)
          ·
            refine ⟨10315763226629296595331841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55017403875356248508436485 10315763226629296595331841)
            ·
              refine ⟨7736822419971972446498881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10315763226629296595331841 7736822419971972446498881)
              ·
                refine ⟨5802616814978979334874161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7736822419971972446498881 5802616814978979334874161)
                ·
                  refine ⟨4351962611234234501155621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5802616814978979334874161 4351962611234234501155621)
                  ·
                    refine ⟨815992989606418968966679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4351962611234234501155621 815992989606418968966679)
                    ·
                      rfl

theorem cell22_2383711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 2, 2, 4].length) (baseStart_2383711 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383711 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383711 prefixEnd_2383711 := by exact prefixLift 2383711
  have htrace : WordTrace (prefixWord ++ tailWord_2383711) baseStart_2383711 baseEnd_2383711 := by
    simpa [prefixWord, tailWord_2383711, baseEnd_2383711] using wordTrace_append hprefix tailTrace_2383711
  have hstable : (prefixWord ++ tailWord_2383711).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383711).length < 2 ^ (prefixWord ++ tailWord_2383711).sum := by decide
  have hdescent : baseEnd_2383711 < baseStart_2383711 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383713 : List Nat := [1, 2, 3, 1, 1, 1, 6, 2, 2, 3]
def baseStart_2383713 : Nat := 118140960795 + 2383713 * 2 ^ 59
def prefixEnd_2383713 : Nat := 4983230072969 + 3 ^ 40 * 2383713 * 2
def baseEnd_2383713 : Nat := 815993674247291630416673

theorem tailTrace_2383713 : CollatzResearch.WordTrace tailWord_2383713 prefixEnd_2383713 815993674247291630416673 := by
  unfold tailWord_2383713
  simp only [CollatzResearch.WordTrace]
  refine ⟨86941155613222381614163793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57960770408814921076109195 86941155613222381614163793)
  ·
    refine ⟨65205866709916786210622845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86941155613222381614163793 65205866709916786210622845)
    ·
      refine ⟨24452200016218794828983567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65205866709916786210622845 24452200016218794828983567)
      ·
        refine ⟨36678300024328192243475351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24452200016218794828983567 36678300024328192243475351)
        ·
          refine ⟨55017450036492288365213027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36678300024328192243475351 55017450036492288365213027)
          ·
            refine ⟨82526175054738432547819541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55017450036492288365213027 82526175054738432547819541)
            ·
              refine ⟨3868414455690864025679041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82526175054738432547819541 3868414455690864025679041)
              ·
                refine ⟨2901310841768148019259281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3868414455690864025679041 2901310841768148019259281)
                ·
                  refine ⟨2175983131326111014444461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2901310841768148019259281 2175983131326111014444461)
                  ·
                    refine ⟨815993674247291630416673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2175983131326111014444461 815993674247291630416673)
                    ·
                      rfl

theorem cell22_2383713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 6, 2, 2, 3].length) (baseStart_2383713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383713 prefixEnd_2383713 := by exact prefixLift 2383713
  have htrace : WordTrace (prefixWord ++ tailWord_2383713) baseStart_2383713 baseEnd_2383713 := by
    simpa [prefixWord, tailWord_2383713, baseEnd_2383713] using wordTrace_append hprefix tailTrace_2383713
  have hstable : (prefixWord ++ tailWord_2383713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383713).length < 2 ^ (prefixWord ++ tailWord_2383713).sum := by decide
  have hdescent : baseEnd_2383713 < baseStart_2383713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383739 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 4, 6]
def baseStart_2383739 : Nat := 118140960795 + 2383739 * 2 ^ 59
def prefixEnd_2383739 : Nat := 4983230072969 + 3 ^ 40 * 2383739 * 2
def baseEnd_2383739 : Nat := 816002574578636229266593

theorem tailTrace_2383739 : CollatzResearch.WordTrace tailWord_2383739 prefixEnd_2383739 816002574578636229266593 := by
  unfold tailWord_2383739
  simp only [CollatzResearch.WordTrace]
  refine ⟨86942103911128188054610271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57961402607418792036406847 86942103911128188054610271)
  ·
    refine ⟨130413155866692282081915407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86942103911128188054610271 130413155866692282081915407)
    ·
      refine ⟨195619733800038423122873111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130413155866692282081915407 195619733800038423122873111)
      ·
        refine ⟨293429600700057634684309667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195619733800038423122873111 293429600700057634684309667)
        ·
          refine ⟨440144401050086452026464501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293429600700057634684309667 440144401050086452026464501)
          ·
            refine ⟨41263537598445604877481047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 440144401050086452026464501 41263537598445604877481047)
            ·
              refine ⟨61895306397668407316221571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41263537598445604877481047 61895306397668407316221571)
              ·
                refine ⟨92842959596502610974332357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61895306397668407316221571 92842959596502610974332357)
                ·
                  refine ⟨17408054924344239557687317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 92842959596502610974332357 17408054924344239557687317)
                  ·
                    refine ⟨816002574578636229266593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17408054924344239557687317 816002574578636229266593)
                    ·
                      rfl

theorem cell22_2383739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 4, 6].length) (baseStart_2383739 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383739 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383739 prefixEnd_2383739 := by exact prefixLift 2383739
  have htrace : WordTrace (prefixWord ++ tailWord_2383739) baseStart_2383739 baseEnd_2383739 := by
    simpa [prefixWord, tailWord_2383739, baseEnd_2383739] using wordTrace_append hprefix tailTrace_2383739
  have hstable : (prefixWord ++ tailWord_2383739).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383739).length < 2 ^ (prefixWord ++ tailWord_2383739).sum := by decide
  have hdescent : baseEnd_2383739 < baseStart_2383739 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383775 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 3, 3]
def baseStart_2383775 : Nat := 118140960795 + 2383775 * 2 ^ 59
def prefixEnd_2383775 : Nat := 4983230072969 + 3 ^ 40 * 2383775 * 2
def baseEnd_2383775 : Nat := 816014898114344135366483

theorem tailTrace_2383775 : CollatzResearch.WordTrace tailWord_2383775 prefixEnd_2383775 816014898114344135366483 := by
  unfold tailWord_2383775
  simp only [CollatzResearch.WordTrace]
  refine ⟨86943416938997766202920779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57962277959331844135280519 86943416938997766202920779)
  ·
    refine ⟨130415125408496649304381169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86943416938997766202920779 130415125408496649304381169)
    ·
      refine ⟨97811344056372486978285877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130415125408496649304381169 97811344056372486978285877)
      ·
        refine ⟨9169813505284920654214301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97811344056372486978285877 9169813505284920654214301)
        ·
          refine ⟨3438680064481845245330363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9169813505284920654214301 3438680064481845245330363)
          ·
            refine ⟨5158020096722767867995545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438680064481845245330363 5158020096722767867995545)
            ·
              refine ⟨3868515072542075900996659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5158020096722767867995545 3868515072542075900996659)
              ·
                refine ⟨5802772608813113851494989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3868515072542075900996659 5802772608813113851494989)
                ·
                  refine ⟨2176039728304917694310621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5802772608813113851494989 2176039728304917694310621)
                  ·
                    refine ⟨816014898114344135366483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2176039728304917694310621 816014898114344135366483)
                    ·
                      rfl

theorem cell22_2383775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 3, 3].length) (baseStart_2383775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383775 prefixEnd_2383775 := by exact prefixLift 2383775
  have htrace : WordTrace (prefixWord ++ tailWord_2383775) baseStart_2383775 baseEnd_2383775 := by
    simpa [prefixWord, tailWord_2383775, baseEnd_2383775] using wordTrace_append hprefix tailTrace_2383775
  have hstable : (prefixWord ++ tailWord_2383775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383775).length < 2 ^ (prefixWord ++ tailWord_2383775).sum := by decide
  have hdescent : baseEnd_2383775 < baseStart_2383775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383818 : List Nat := [3, 1, 2, 1, 2, 1, 4, 3, 1, 4]
def baseStart_2383818 : Nat := 118140960795 + 2383818 * 2 ^ 59
def prefixEnd_2383818 : Nat := 4983230072969 + 3 ^ 40 * 2383818 * 2
def baseEnd_2383818 : Nat := 816029617893106356541351

theorem tailTrace_2383818 : CollatzResearch.WordTrace tailWord_2383818 prefixEnd_2383818 816029617893106356541351 := by
  unfold tailWord_2383818
  simp only [CollatzResearch.WordTrace]
  refine ⟨21736246319460496136684027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57963323518561323031157405 21736246319460496136684027)
  ·
    refine ⟨32604369479190744205026041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21736246319460496136684027 32604369479190744205026041)
    ·
      refine ⟨24453277109393058153769531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32604369479190744205026041 24453277109393058153769531)
      ·
        refine ⟨36679915664089587230654297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24453277109393058153769531 36679915664089587230654297)
        ·
          refine ⟨27509936748067190422990723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36679915664089587230654297 27509936748067190422990723)
          ·
            refine ⟨41264905122100785634486085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27509936748067190422990723 41264905122100785634486085)
            ·
              refine ⟨7737169710393897306466141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41264905122100785634486085 7737169710393897306466141)
              ·
                refine ⟨2901438641397711489924803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7737169710393897306466141 2901438641397711489924803)
                ·
                  refine ⟨4352157962096567234887205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2901438641397711489924803 4352157962096567234887205)
                  ·
                    refine ⟨816029617893106356541351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4352157962096567234887205 816029617893106356541351)
                    ·
                      rfl

theorem cell22_2383818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_2383818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383818 prefixEnd_2383818 := by exact prefixLift 2383818
  have htrace : WordTrace (prefixWord ++ tailWord_2383818) baseStart_2383818 baseEnd_2383818 := by
    simpa [prefixWord, tailWord_2383818, baseEnd_2383818] using wordTrace_append hprefix tailTrace_2383818
  have hstable : (prefixWord ++ tailWord_2383818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383818).length < 2 ^ (prefixWord ++ tailWord_2383818).sum := by decide
  have hdescent : baseEnd_2383818 < baseStart_2383818 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383882 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 2, 3]
def baseStart_2383882 : Nat := 118140960795 + 2383882 * 2 ^ 59
def prefixEnd_2383882 : Nat := 4983230072969 + 3 ^ 40 * 2383882 * 2
def baseEnd_2383882 : Nat := 816051526401031522941155

theorem tailTrace_2383882 : CollatzResearch.WordTrace tailWord_2383882 prefixEnd_2383882 816051526401031522941155 := by
  unfold tailWord_2383882
  simp only [CollatzResearch.WordTrace]
  refine ⟨21736829887402530869266475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57964879699740082318043933 21736829887402530869266475)
  ·
    refine ⟨32605244831103796303899713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21736829887402530869266475 32605244831103796303899713)
    ·
      refine ⟨24453933623327847227924785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32605244831103796303899713 24453933623327847227924785)
      ·
        refine ⟨18340450217495885420943589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24453933623327847227924785 18340450217495885420943589)
        ·
          refine ⟨3438834415780478516426923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18340450217495885420943589 3438834415780478516426923)
          ·
            refine ⟨5158251623670717774640385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438834415780478516426923 5158251623670717774640385)
            ·
              refine ⟨3868688717753038330980289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5158251623670717774640385 3868688717753038330980289)
              ·
                refine ⟨2901516538314778748235217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3868688717753038330980289 2901516538314778748235217)
                ·
                  refine ⟨2176137403736084061176413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2901516538314778748235217 2176137403736084061176413)
                  ·
                    refine ⟨816051526401031522941155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2176137403736084061176413 816051526401031522941155)
                    ·
                      rfl

theorem cell22_2383882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 2, 3].length) (baseStart_2383882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383882 prefixEnd_2383882 := by exact prefixLift 2383882
  have htrace : WordTrace (prefixWord ++ tailWord_2383882) baseStart_2383882 baseEnd_2383882 := by
    simpa [prefixWord, tailWord_2383882, baseEnd_2383882] using wordTrace_append hprefix tailTrace_2383882
  have hstable : (prefixWord ++ tailWord_2383882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383882).length < 2 ^ (prefixWord ++ tailWord_2383882).sum := by decide
  have hdescent : baseEnd_2383882 < baseStart_2383882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383891 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 2, 6]
def baseStart_2383891 : Nat := 118140960795 + 2383891 * 2 ^ 59
def prefixEnd_2383891 : Nat := 4983230072969 + 3 ^ 40 * 2383891 * 2
def baseEnd_2383891 : Nat := 816054607284958499466127

theorem tailTrace_2383891 : CollatzResearch.WordTrace tailWord_2383891 prefixEnd_2383891 816054607284958499466127 := by
  unfold tailWord_2383891
  simp only [CollatzResearch.WordTrace]
  refine ⟨86947647806577518014143527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57965098537718345342762351 86947647806577518014143527)
  ·
    refine ⟨130421471709866277021215291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86947647806577518014143527 130421471709866277021215291)
    ·
      refine ⟨195632207564799415531822937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130421471709866277021215291 195632207564799415531822937)
      ·
        refine ⟨146724155673599561648867203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195632207564799415531822937 146724155673599561648867203)
        ·
          refine ⟨220086233510399342473300805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146724155673599561648867203 220086233510399342473300805)
          ·
            refine ⟨41266168783199876713743901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220086233510399342473300805 41266168783199876713743901)
            ·
              refine ⟨15474813293699953767653963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41266168783199876713743901 15474813293699953767653963)
              ·
                refine ⟨23212219940549930651480945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15474813293699953767653963 23212219940549930651480945)
                ·
                  refine ⟨17409164955412447988610709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23212219940549930651480945 17409164955412447988610709)
                  ·
                    refine ⟨816054607284958499466127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17409164955412447988610709 816054607284958499466127)
                    ·
                      rfl

theorem cell22_2383891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 2, 6].length) (baseStart_2383891 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383891 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383891 prefixEnd_2383891 := by exact prefixLift 2383891
  have htrace : WordTrace (prefixWord ++ tailWord_2383891) baseStart_2383891 baseEnd_2383891 := by
    simpa [prefixWord, tailWord_2383891, baseEnd_2383891] using wordTrace_append hprefix tailTrace_2383891
  have hstable : (prefixWord ++ tailWord_2383891).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383891).length < 2 ^ (prefixWord ++ tailWord_2383891).sum := by decide
  have hdescent : baseEnd_2383891 < baseStart_2383891 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383895 : List Nat := [1, 1, 3, 5, 2, 2, 1, 7]
def baseStart_2383895 : Nat := 118140960795 + 2383895 * 2 ^ 59
def prefixEnd_2383895 : Nat := 4983230072969 + 3 ^ 40 * 2383895 * 2
def baseEnd_2383895 : Nat := 90672886285189313596235

theorem tailTrace_2383895 : CollatzResearch.WordTrace tailWord_2383895 prefixEnd_2383895 90672886285189313596235 := by
  unfold tailWord_2383895
  simp only [CollatzResearch.WordTrace]
  refine ⟨86947793698563026697289139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57965195799042017798192759 86947793698563026697289139)
  ·
    refine ⟨130421690547844540045933709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86947793698563026697289139 130421690547844540045933709)
    ·
      refine ⟨48908133955441702517225141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130421690547844540045933709 48908133955441702517225141)
      ·
        refine ⟨4585137558322659610989857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 48908133955441702517225141 4585137558322659610989857)
        ·
          refine ⟨3438853168741994708242393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4585137558322659610989857 3438853168741994708242393)
          ·
            refine ⟨2579139876556496031181795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3438853168741994708242393 2579139876556496031181795)
            ·
              refine ⟨3868709814834744046772693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2579139876556496031181795 3868709814834744046772693)
              ·
                refine ⟨90672886285189313596235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3868709814834744046772693 90672886285189313596235)
                ·
                  rfl

theorem cell22_2383895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 7].length) (baseStart_2383895 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383895 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383895 prefixEnd_2383895 := by exact prefixLift 2383895
  have htrace : WordTrace (prefixWord ++ tailWord_2383895) baseStart_2383895 baseEnd_2383895 := by
    simpa [prefixWord, tailWord_2383895, baseEnd_2383895] using wordTrace_append hprefix tailTrace_2383895
  have hstable : (prefixWord ++ tailWord_2383895).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383895).length < 2 ^ (prefixWord ++ tailWord_2383895).sum := by decide
  have hdescent : baseEnd_2383895 < baseStart_2383895 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383912 : List Nat := [2, 1, 5, 3, 1, 1, 3, 6]
def baseStart_2383912 : Nat := 118140960795 + 2383912 * 2 ^ 59
def prefixEnd_2383912 : Nat := 4983230072969 + 3 ^ 40 * 2383912 * 2
def baseEnd_2383912 : Nat := 90673532890457938299007

theorem tailTrace_2383912 : CollatzResearch.WordTrace tailWord_2383912 prefixEnd_2383912 90673532890457938299007 := by
  unfold tailWord_2383912
  simp only [CollatzResearch.WordTrace]
  refine ⟨43474206869750719300328995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57965609159667625733771993 43474206869750719300328995)
  ·
    refine ⟨65211310304626078950493493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43474206869750719300328995 65211310304626078950493493)
    ·
      refine ⟨6113560341058694901608765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65211310304626078950493493 6113560341058694901608765)
      ·
        refine ⟨2292585127897010588103287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6113560341058694901608765 2292585127897010588103287)
        ·
          refine ⟨3438877691845515882154931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292585127897010588103287 3438877691845515882154931)
          ·
            refine ⟨5158316537768273823232397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3438877691845515882154931 5158316537768273823232397)
            ·
              refine ⟨1934368701663102683712149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5158316537768273823232397 1934368701663102683712149)
              ·
                refine ⟨90673532890457938299007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1934368701663102683712149 90673532890457938299007)
                ·
                  rfl

theorem cell22_2383912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 3, 6].length) (baseStart_2383912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383912 prefixEnd_2383912 := by exact prefixLift 2383912
  have htrace : WordTrace (prefixWord ++ tailWord_2383912) baseStart_2383912 baseEnd_2383912 := by
    simpa [prefixWord, tailWord_2383912, baseEnd_2383912] using wordTrace_append hprefix tailTrace_2383912
  have hstable : (prefixWord ++ tailWord_2383912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383912).length < 2 ^ (prefixWord ++ tailWord_2383912).sum := by decide
  have hdescent : baseEnd_2383912 < baseStart_2383912 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383951 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 10]
def baseStart_2383951 : Nat := 118140960795 + 2383951 * 2 ^ 59
def prefixEnd_2383951 : Nat := 4983230072969 + 3 ^ 40 * 2383951 * 2
def baseEnd_2383951 : Nat := 272025048837046114321981

theorem tailTrace_2383951 : CollatzResearch.WordTrace tailWord_2383951 prefixEnd_2383951 272025048837046114321981 := by
  unfold tailWord_2383951
  simp only [CollatzResearch.WordTrace]
  refine ⟨86949836186360148261327707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57966557457573432174218471 86949836186360148261327707)
  ·
    refine ⟨130424754279540222391991561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86949836186360148261327707 130424754279540222391991561)
    ·
      refine ⟨97818565709655166793993671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130424754279540222391991561 97818565709655166793993671)
      ·
        refine ⟨146727848564482750190990507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97818565709655166793993671 146727848564482750190990507)
        ·
          refine ⟨220091772846724125286485761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146727848564482750190990507 220091772846724125286485761)
          ·
            refine ⟨165068829635043093964864321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220091772846724125286485761 165068829635043093964864321)
            ·
              refine ⟨123801622226282320473648241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165068829635043093964864321 123801622226282320473648241)
              ·
                refine ⟨92851216669711740355236181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 123801622226282320473648241 92851216669711740355236181)
                ·
                  refine ⟨272025048837046114321981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 92851216669711740355236181 272025048837046114321981)
                  ·
                    rfl

theorem cell22_2383951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 10].length) (baseStart_2383951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383951 prefixEnd_2383951 := by exact prefixLift 2383951
  have htrace : WordTrace (prefixWord ++ tailWord_2383951) baseStart_2383951 baseEnd_2383951 := by
    simpa [prefixWord, tailWord_2383951, baseEnd_2383951] using wordTrace_append hprefix tailTrace_2383951
  have hstable : (prefixWord ++ tailWord_2383951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383951).length < 2 ^ (prefixWord ++ tailWord_2383951).sum := by decide
  have hdescent : baseEnd_2383951 < baseStart_2383951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2383968 : List Nat := [2, 1, 1, 3, 2, 3, 2, 2, 6]
def baseStart_2383968 : Nat := 118140960795 + 2383968 * 2 ^ 59
def prefixEnd_2383968 : Nat := 4983230072969 + 3 ^ 40 * 2383968 * 2
def baseEnd_2383968 : Nat := 272026988652851988430297

theorem tailTrace_2383968 : CollatzResearch.WordTrace tailWord_2383968 prefixEnd_2383968 272026988652851988430297 := by
  unfold tailWord_2383968
  simp only [CollatzResearch.WordTrace]
  refine ⟨43475228113649280082348279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57966970818199040109797705 43475228113649280082348279)
  ·
    refine ⟨65212842170473920123522419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43475228113649280082348279 65212842170473920123522419)
    ·
      refine ⟨97819263255710880185283629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65212842170473920123522419 97819263255710880185283629)
      ·
        refine ⟨36682223720891580069481361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97819263255710880185283629 36682223720891580069481361)
        ·
          refine ⟨27511667790668685052111021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36682223720891580069481361 27511667790668685052111021)
          ·
            refine ⟨10316875421500756894541633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27511667790668685052111021 10316875421500756894541633)
            ·
              refine ⟨7737656566125567670906225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10316875421500756894541633 7737656566125567670906225)
              ·
                refine ⟨5803242424594175753179669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7737656566125567670906225 5803242424594175753179669)
                ·
                  refine ⟨272026988652851988430297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5803242424594175753179669 272026988652851988430297)
                  ·
                    rfl

theorem cell22_2383968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 2, 6].length) (baseStart_2383968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2383968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2383968 prefixEnd_2383968 := by exact prefixLift 2383968
  have htrace : WordTrace (prefixWord ++ tailWord_2383968) baseStart_2383968 baseEnd_2383968 := by
    simpa [prefixWord, tailWord_2383968, baseEnd_2383968] using wordTrace_append hprefix tailTrace_2383968
  have hstable : (prefixWord ++ tailWord_2383968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2383968).length < 2 ^ (prefixWord ++ tailWord_2383968).sum := by decide
  have hdescent : baseEnd_2383968 < baseStart_2383968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2383968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384000 : List Nat := [2, 1, 1, 2, 1, 3, 1, 6, 2, 3]
def baseStart_2384000 : Nat := 118140960795 + 2384000 * 2 ^ 59
def prefixEnd_2384000 : Nat := 4983230072969 + 3 ^ 40 * 2384000 * 2
def baseEnd_2384000 : Nat := 816091920212518548490793

theorem tailTrace_2384000 : CollatzResearch.WordTrace tailWord_2384000 prefixEnd_2384000 816091920212518548490793 := by
  unfold tailWord_2384000
  simp only [CollatzResearch.WordTrace]
  refine ⟨43475811681591314814930727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57967748908788419753240969 43475811681591314814930727)
  ·
    refine ⟨65213717522386972222396091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43475811681591314814930727 65213717522386972222396091)
    ·
      refine ⟨97820576283580458333594137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65213717522386972222396091 97820576283580458333594137)
      ·
        refine ⟨73365432212685343750195603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97820576283580458333594137 73365432212685343750195603)
        ·
          refine ⟨110048148319028015625293405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73365432212685343750195603 110048148319028015625293405)
          ·
            refine ⟨41268055619635505859485027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110048148319028015625293405 41268055619635505859485027)
            ·
              refine ⟨61902083429453258789227541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41268055619635505859485027 61902083429453258789227541)
              ·
                refine ⟨2901660160755621505745041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 61902083429453258789227541 2901660160755621505745041)
                ·
                  refine ⟨2176245120566716129308781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2901660160755621505745041 2176245120566716129308781)
                  ·
                    refine ⟨816091920212518548490793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2176245120566716129308781 816091920212518548490793)
                    ·
                      rfl

theorem cell22_2384000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 1, 6, 2, 3].length) (baseStart_2384000 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384000 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384000 prefixEnd_2384000 := by exact prefixLift 2384000
  have htrace : WordTrace (prefixWord ++ tailWord_2384000) baseStart_2384000 baseEnd_2384000 := by
    simpa [prefixWord, tailWord_2384000, baseEnd_2384000] using wordTrace_append hprefix tailTrace_2384000
  have hstable : (prefixWord ++ tailWord_2384000).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384000).length < 2 ^ (prefixWord ++ tailWord_2384000).sum := by decide
  have hdescent : baseEnd_2384000 < baseStart_2384000 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384053 : List Nat := [1, 3, 3, 4, 2, 1, 2, 2, 4]
def baseStart_2384053 : Nat := 118140960795 + 2384053 * 2 ^ 59
def prefixEnd_2384053 : Nat := 4983230072969 + 3 ^ 40 * 2384053 * 2
def baseEnd_2384053 : Nat := 272036687731881358971877

theorem tailTrace_2384053 : CollatzResearch.WordTrace tailWord_2384053 prefixEnd_2384053 272036687731881358971877 := by
  unfold tailWord_2384053
  simp only [CollatzResearch.WordTrace]
  refine ⟨86953556431990619681540813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57969037621327079787693875 86953556431990619681540813)
  ·
    refine ⟨32607583661996482380577805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86953556431990619681540813 32607583661996482380577805)
    ·
      refine ⟨12227843873248680892716677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32607583661996482380577805 12227843873248680892716677)
      ·
        refine ⟨2292720726234127667384377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12227843873248680892716677 2292720726234127667384377)
        ·
          refine ⟨1719540544675595750538283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2292720726234127667384377 1719540544675595750538283)
          ·
            refine ⟨2579310817013393625807425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719540544675595750538283 2579310817013393625807425)
            ·
              refine ⟨1934483112760045219355569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2579310817013393625807425 1934483112760045219355569)
              ·
                refine ⟨1450862334570033914516677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1934483112760045219355569 1450862334570033914516677)
                ·
                  refine ⟨272036687731881358971877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1450862334570033914516677 272036687731881358971877)
                  ·
                    rfl

theorem cell22_2384053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 2, 2, 4].length) (baseStart_2384053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384053 prefixEnd_2384053 := by exact prefixLift 2384053
  have htrace : WordTrace (prefixWord ++ tailWord_2384053) baseStart_2384053 baseEnd_2384053 := by
    simpa [prefixWord, tailWord_2384053, baseEnd_2384053] using wordTrace_append hprefix tailTrace_2384053
  have hstable : (prefixWord ++ tailWord_2384053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384053).length < 2 ^ (prefixWord ++ tailWord_2384053).sum := by decide
  have hdescent : baseEnd_2384053 < baseStart_2384053 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384058 : List Nat := [3, 1, 1, 1, 2, 2, 2, 3, 7]
def baseStart_2384058 : Nat := 118140960795 + 2384058 * 2 ^ 59
def prefixEnd_2384058 : Nat := 4983230072969 + 3 ^ 40 * 2384058 * 2
def baseEnd_2384058 : Nat := 272037258265941910180205

theorem tailTrace_2384058 : CollatzResearch.WordTrace tailWord_2384058 prefixEnd_2384058 272037258265941910180205 := by
  unfold tailWord_2384058
  simp only [CollatzResearch.WordTrace]
  refine ⟨21738434699243126383868207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57969159197981670356981885 21738434699243126383868207)
  ·
    refine ⟨32607652048864689575802311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21738434699243126383868207 32607652048864689575802311)
    ·
      refine ⟨48911478073297034363703467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32607652048864689575802311 48911478073297034363703467)
      ·
        refine ⟨73367217109945551545555201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48911478073297034363703467 73367217109945551545555201)
        ·
          refine ⟨55025412832459163659166401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73367217109945551545555201 55025412832459163659166401)
          ·
            refine ⟨41269059624344372744374801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55025412832459163659166401 41269059624344372744374801)
            ·
              refine ⟨30951794718258279558281101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41269059624344372744374801 30951794718258279558281101)
              ·
                refine ⟨11606923019346854834355413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30951794718258279558281101 11606923019346854834355413)
                ·
                  refine ⟨272037258265941910180205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11606923019346854834355413 272037258265941910180205)
                  ·
                    rfl

theorem cell22_2384058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 3, 7].length) (baseStart_2384058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384058 prefixEnd_2384058 := by exact prefixLift 2384058
  have htrace : WordTrace (prefixWord ++ tailWord_2384058) baseStart_2384058 baseEnd_2384058 := by
    simpa [prefixWord, tailWord_2384058, baseEnd_2384058] using wordTrace_append hprefix tailTrace_2384058
  have hstable : (prefixWord ++ tailWord_2384058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384058).length < 2 ^ (prefixWord ++ tailWord_2384058).sum := by decide
  have hdescent : baseEnd_2384058 < baseStart_2384058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384105 : List Nat := [1, 2, 1, 1, 1, 2, 2, 7, 1, 4]
def baseStart_2384105 : Nat := 118140960795 + 2384105 * 2 ^ 59
def prefixEnd_2384105 : Nat := 4983230072969 + 3 ^ 40 * 2384105 * 2
def baseEnd_2384105 : Nat := 816127863858333274615471

theorem tailTrace_2384105 : CollatzResearch.WordTrace tailWord_2384105 prefixEnd_2384105 816127863858333274615471 := by
  unfold tailWord_2384105
  simp only [CollatzResearch.WordTrace]
  refine ⟨86955453027802232562433769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57970302018534821708289179 86955453027802232562433769)
  ·
    refine ⟨65216589770851674421825327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86955453027802232562433769 65216589770851674421825327)
    ·
      refine ⟨97824884656277511632737991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65216589770851674421825327 97824884656277511632737991)
      ·
        refine ⟨146737326984416267449106987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97824884656277511632737991 146737326984416267449106987)
        ·
          refine ⟨220105990476624401173660481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146737326984416267449106987 220105990476624401173660481)
          ·
            refine ⟨165079492857468300880245361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220105990476624401173660481 165079492857468300880245361)
            ·
              refine ⟨123809619643101225660184021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165079492857468300880245361 123809619643101225660184021)
              ·
                refine ⟨2901787960385184976410563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 123809619643101225660184021 2901787960385184976410563)
                ·
                  refine ⟨4352681940577777464615845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2901787960385184976410563 4352681940577777464615845)
                  ·
                    refine ⟨816127863858333274615471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4352681940577777464615845 816127863858333274615471)
                    ·
                      rfl

theorem cell22_2384105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 7, 1, 4].length) (baseStart_2384105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384105 prefixEnd_2384105 := by exact prefixLift 2384105
  have htrace : WordTrace (prefixWord ++ tailWord_2384105) baseStart_2384105 baseEnd_2384105 := by
    simpa [prefixWord, tailWord_2384105, baseEnd_2384105] using wordTrace_append hprefix tailTrace_2384105
  have hstable : (prefixWord ++ tailWord_2384105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384105).length < 2 ^ (prefixWord ++ tailWord_2384105).sum := by decide
  have hdescent : baseEnd_2384105 < baseStart_2384105 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384109 : List Nat := [1, 5, 1, 2, 3, 2, 1, 2, 5]
def baseStart_2384109 : Nat := 118140960795 + 2384109 * 2 ^ 59
def prefixEnd_2384109 : Nat := 4983230072969 + 3 ^ 40 * 2384109 * 2
def baseEnd_2384109 : Nat := 272043077713359532505153

theorem tailTrace_2384109 : CollatzResearch.WordTrace tailWord_2384109 prefixEnd_2384109 272043077713359532505153 := by
  unfold tailWord_2384109
  simp only [CollatzResearch.WordTrace]
  refine ⟨86955598919787741245579381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57970399279858494163719587 86955598919787741245579381)
  ·
    refine ⟨8152087398730100741773067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 86955598919787741245579381 8152087398730100741773067)
    ·
      refine ⟨12228131098095151112659601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8152087398730100741773067 12228131098095151112659601)
      ·
        refine ⟨9171098323571363334494701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12228131098095151112659601 9171098323571363334494701)
        ·
          refine ⟨3439161871339261250435513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9171098323571363334494701 3439161871339261250435513)
          ·
            refine ⟨2579371403504445937826635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3439161871339261250435513 2579371403504445937826635)
            ·
              refine ⟨3869057105256668906739953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2579371403504445937826635 3869057105256668906739953)
              ·
                refine ⟨2901792828942501680054965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3869057105256668906739953 2901792828942501680054965)
                ·
                  refine ⟨272043077713359532505153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2901792828942501680054965 272043077713359532505153)
                  ·
                    rfl

theorem cell22_2384109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_2384109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384109 prefixEnd_2384109 := by exact prefixLift 2384109
  have htrace : WordTrace (prefixWord ++ tailWord_2384109) baseStart_2384109 baseEnd_2384109 := by
    simpa [prefixWord, tailWord_2384109, baseEnd_2384109] using wordTrace_append hprefix tailTrace_2384109
  have hstable : (prefixWord ++ tailWord_2384109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384109).length < 2 ^ (prefixWord ++ tailWord_2384109).sum := by decide
  have hdescent : baseEnd_2384109 < baseStart_2384109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384186 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 2, 3]
def baseStart_2384186 : Nat := 118140960795 + 2384186 * 2 ^ 59
def prefixEnd_2384186 : Nat := 4983230072969 + 3 ^ 40 * 2384186 * 2
def baseEnd_2384186 : Nat := 816155591813676063340223

theorem tailTrace_2384186 : CollatzResearch.WordTrace tailWord_2384186 prefixEnd_2384186 816155591813676063340223 := by
  unfold tailWord_2384186
  simp only [CollatzResearch.WordTrace]
  refine ⟨21739601835127195849033103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57972271560339188930754941 21739601835127195849033103)
  ·
    refine ⟨32609402752690793773549655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21739601835127195849033103 32609402752690793773549655)
    ·
      refine ⟨48914104129036190660324483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32609402752690793773549655 48914104129036190660324483)
      ·
        refine ⟨73371156193554285990486725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48914104129036190660324483 73371156193554285990486725)
        ·
          refine ⟨13757091786291428623216261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73371156193554285990486725 13757091786291428623216261)
          ·
            refine ⟨2579454709929642866853049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13757091786291428623216261 2579454709929642866853049)
            ·
              refine ⟨1934591032447232150139787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2579454709929642866853049 1934591032447232150139787)
              ·
                refine ⟨2901886548670848225209681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934591032447232150139787 2901886548670848225209681)
                ·
                  refine ⟨2176414911503136168907261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2901886548670848225209681 2176414911503136168907261)
                  ·
                    refine ⟨816155591813676063340223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2176414911503136168907261 816155591813676063340223)
                    ·
                      rfl

theorem cell22_2384186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 2, 3].length) (baseStart_2384186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384186 prefixEnd_2384186 := by exact prefixLift 2384186
  have htrace : WordTrace (prefixWord ++ tailWord_2384186) baseStart_2384186 baseEnd_2384186 := by
    simpa [prefixWord, tailWord_2384186, baseEnd_2384186] using wordTrace_append hprefix tailTrace_2384186
  have hstable : (prefixWord ++ tailWord_2384186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384186).length < 2 ^ (prefixWord ++ tailWord_2384186).sum := by decide
  have hdescent : baseEnd_2384186 < baseStart_2384186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384210 : List Nat := [3, 2, 2, 1, 1, 1, 2, 1, 9]
def baseStart_2384210 : Nat := 118140960795 + 2384210 * 2 ^ 59
def prefixEnd_2384210 : Nat := 4983230072969 + 3 ^ 40 * 2384210 * 2
def baseEnd_2384210 : Nat := 272054602501382666913383

theorem tailTrace_2384210 : CollatzResearch.WordTrace tailWord_2384210 prefixEnd_2384210 272054602501382666913383 := by
  unfold tailWord_2384210
  simp only [CollatzResearch.WordTrace]
  refine ⟨21739820673105458873751521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57972855128281223663337389 21739820673105458873751521)
  ·
    refine ⟨16304865504829094155313641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21739820673105458873751521 16304865504829094155313641)
    ·
      refine ⟨12228649128621820616485231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16304865504829094155313641 12228649128621820616485231)
      ·
        refine ⟨18342973692932730924727847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12228649128621820616485231 18342973692932730924727847)
        ·
          refine ⟨27514460539399096387091771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18342973692932730924727847 27514460539399096387091771)
          ·
            refine ⟨41271690809098644580637657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27514460539399096387091771 41271690809098644580637657)
            ·
              refine ⟨30953768106823983435478243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41271690809098644580637657 30953768106823983435478243)
              ·
                refine ⟨46430652160235975153217365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30953768106823983435478243 46430652160235975153217365)
                ·
                  refine ⟨272054602501382666913383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46430652160235975153217365 272054602501382666913383)
                  ·
                    rfl

theorem cell22_2384210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 1, 9].length) (baseStart_2384210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384210 prefixEnd_2384210 := by exact prefixLift 2384210
  have htrace : WordTrace (prefixWord ++ tailWord_2384210) baseStart_2384210 baseEnd_2384210 := by
    simpa [prefixWord, tailWord_2384210, baseEnd_2384210] using wordTrace_append hprefix tailTrace_2384210
  have hstable : (prefixWord ++ tailWord_2384210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384210).length < 2 ^ (prefixWord ++ tailWord_2384210).sum := by decide
  have hdescent : baseEnd_2384210 < baseStart_2384210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384227 : List Nat := [1, 1, 1, 5, 2, 1, 4, 2, 5]
def baseStart_2384227 : Nat := 118140960795 + 2384227 * 2 ^ 59
def prefixEnd_2384227 : Nat := 4983230072969 + 3 ^ 40 * 2384227 * 2
def baseEnd_2384227 : Nat := 272056542317188541021699

theorem tailTrace_2384227 : CollatzResearch.WordTrace tailWord_2384227 prefixEnd_2384227 272056542317188541021699 := by
  unfold tailWord_2384227
  simp only [CollatzResearch.WordTrace]
  refine ⟨86959902733360247398374935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57973268488906831598916623 86959902733360247398374935)
  ·
    refine ⟨130439854100040371097562403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86959902733360247398374935 130439854100040371097562403)
    ·
      refine ⟨195659781150060556646343605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130439854100040371097562403 195659781150060556646343605)
      ·
        refine ⟨18343104482818177185594713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 195659781150060556646343605 18343104482818177185594713)
        ·
          refine ⟨13757328362113632889196035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18343104482818177185594713 13757328362113632889196035)
          ·
            refine ⟨20635992543170449333794053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13757328362113632889196035 20635992543170449333794053)
            ·
              refine ⟨3869248601844459250086385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20635992543170449333794053 3869248601844459250086385)
              ·
                refine ⟨2901936451383344437564789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3869248601844459250086385 2901936451383344437564789)
                ·
                  refine ⟨272056542317188541021699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2901936451383344437564789 272056542317188541021699)
                  ·
                    rfl

theorem cell22_2384227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 4, 2, 5].length) (baseStart_2384227 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384227 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384227 prefixEnd_2384227 := by exact prefixLift 2384227
  have htrace : WordTrace (prefixWord ++ tailWord_2384227) baseStart_2384227 baseEnd_2384227 := by
    simpa [prefixWord, tailWord_2384227, baseEnd_2384227] using wordTrace_append hprefix tailTrace_2384227
  have hstable : (prefixWord ++ tailWord_2384227).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384227).length < 2 ^ (prefixWord ++ tailWord_2384227).sum := by decide
  have hdescent : baseEnd_2384227 < baseStart_2384227 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384231 : List Nat := [1, 1, 5, 1, 3, 2, 1, 4, 1, 3]
def baseStart_2384231 : Nat := 118140960795 + 2384231 * 2 ^ 59
def prefixEnd_2384231 : Nat := 4983230072969 + 3 ^ 40 * 2384231 * 2
def baseEnd_2384231 : Nat := 816170996233310945965085

theorem tailTrace_2384231 : CollatzResearch.WordTrace tailWord_2384231 prefixEnd_2384231 816170996233310945965085 := by
  unfold tailWord_2384231
  simp only [CollatzResearch.WordTrace]
  refine ⟨86960048625345756081520547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57973365750230504054347031 86960048625345756081520547)
  ·
    refine ⟨130440072938018634122280821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86960048625345756081520547 130440072938018634122280821)
    ·
      refine ⟨12228756837939246948963827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 130440072938018634122280821 12228756837939246948963827)
      ·
        refine ⟨18343135256908870423445741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12228756837939246948963827 18343135256908870423445741)
        ·
          refine ⟨6878675721340826408792153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18343135256908870423445741 6878675721340826408792153)
          ·
            refine ⟨5159006791005619806594115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6878675721340826408792153 5159006791005619806594115)
            ·
              refine ⟨7738510186508429709891173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159006791005619806594115 7738510186508429709891173)
              ·
                refine ⟨1450970659970330570604595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7738510186508429709891173 1450970659970330570604595)
                ·
                  refine ⟨2176455989955495855906893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1450970659970330570604595 2176455989955495855906893)
                  ·
                    refine ⟨816170996233310945965085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2176455989955495855906893 816170996233310945965085)
                    ·
                      rfl

theorem cell22_2384231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_2384231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384231 prefixEnd_2384231 := by exact prefixLift 2384231
  have htrace : WordTrace (prefixWord ++ tailWord_2384231) baseStart_2384231 baseEnd_2384231 := by
    simpa [prefixWord, tailWord_2384231, baseEnd_2384231] using wordTrace_append hprefix tailTrace_2384231
  have hstable : (prefixWord ++ tailWord_2384231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384231).length < 2 ^ (prefixWord ++ tailWord_2384231).sum := by decide
  have hdescent : baseEnd_2384231 < baseStart_2384231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384242 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 2, 5]
def baseStart_2384242 : Nat := 118140960795 + 2384242 * 2 ^ 59
def prefixEnd_2384242 : Nat := 4983230072969 + 3 ^ 40 * 2384242 * 2
def baseEnd_2384242 : Nat := 816174761758110583940051

theorem tailTrace_2384242 : CollatzResearch.WordTrace tailWord_2384242 prefixEnd_2384242 816174761758110583940051 := by
  unfold tailWord_2384242
  simp only [CollatzResearch.WordTrace]
  refine ⟨21740112457076476240042745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57973633218870603306780653 21740112457076476240042745)
  ·
    refine ⟨16305084342807357180032059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21740112457076476240042745 16305084342807357180032059)
    ·
      refine ⟨24457626514211035770048089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16305084342807357180032059 24457626514211035770048089)
      ·
        refine ⟨18343219885658276827536067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24457626514211035770048089 18343219885658276827536067)
        ·
          refine ⟨27514829828487415241304101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18343219885658276827536067 27514829828487415241304101)
          ·
            refine ⟨5159030592841390357744519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27514829828487415241304101 5159030592841390357744519)
            ·
              refine ⟨7738545889262085536616779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159030592841390357744519 7738545889262085536616779)
              ·
                refine ⟨11607818833893128304925169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7738545889262085536616779 11607818833893128304925169)
                ·
                  refine ⟨8705864125419846228693877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11607818833893128304925169 8705864125419846228693877)
                  ·
                    refine ⟨816174761758110583940051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8705864125419846228693877 816174761758110583940051)
                    ·
                      rfl

theorem cell22_2384242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_2384242 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384242 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384242 prefixEnd_2384242 := by exact prefixLift 2384242
  have htrace : WordTrace (prefixWord ++ tailWord_2384242) baseStart_2384242 baseEnd_2384242 := by
    simpa [prefixWord, tailWord_2384242, baseEnd_2384242] using wordTrace_append hprefix tailTrace_2384242
  have hstable : (prefixWord ++ tailWord_2384242).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384242).length < 2 ^ (prefixWord ++ tailWord_2384242).sum := by decide
  have hdescent : baseEnd_2384242 < baseStart_2384242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384255 : List Nat := [1, 1, 2, 2, 1, 1, 2, 6, 6]
def baseStart_2384255 : Nat := 118140960795 + 2384255 * 2 ^ 59
def prefixEnd_2384255 : Nat := 4983230072969 + 3 ^ 40 * 2384255 * 2
def baseEnd_2384255 : Nat := 272059737307927627788337

theorem tailTrace_2384255 : CollatzResearch.WordTrace tailWord_2384255 prefixEnd_2384255 272059737307927627788337 := by
  unfold tailWord_2384255
  simp only [CollatzResearch.WordTrace]
  refine ⟨86960923977258808180394219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57973949318172538786929479 86960923977258808180394219)
  ·
    refine ⟨130441385965888212270591329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86960923977258808180394219 130441385965888212270591329)
    ·
      refine ⟨97831039474416159202943497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130441385965888212270591329 97831039474416159202943497)
      ·
        refine ⟨73373279605812119402207623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97831039474416159202943497 73373279605812119402207623)
        ·
          refine ⟨110059919408718179103311435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73373279605812119402207623 110059919408718179103311435)
          ·
            refine ⟨165089879113077268654967153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110059919408718179103311435 165089879113077268654967153)
            ·
              refine ⟨123817409334807951491225365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165089879113077268654967153 123817409334807951491225365)
              ·
                refine ⟨5803941062569122726151189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 123817409334807951491225365 5803941062569122726151189)
                ·
                  refine ⟨272059737307927627788337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5803941062569122726151189 272059737307927627788337)
                  ·
                    rfl

theorem cell22_2384255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 6, 6].length) (baseStart_2384255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384255 prefixEnd_2384255 := by exact prefixLift 2384255
  have htrace : WordTrace (prefixWord ++ tailWord_2384255) baseStart_2384255 baseEnd_2384255 := by
    simpa [prefixWord, tailWord_2384255, baseEnd_2384255] using wordTrace_append hprefix tailTrace_2384255
  have hstable : (prefixWord ++ tailWord_2384255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384255).length < 2 ^ (prefixWord ++ tailWord_2384255).sum := by decide
  have hdescent : baseEnd_2384255 < baseStart_2384255 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384278 : List Nat := [5, 3, 1, 2, 1, 1, 1, 1, 7]
def baseStart_2384278 : Nat := 118140960795 + 2384278 * 2 ^ 59
def prefixEnd_2384278 : Nat := 4983230072969 + 3 ^ 40 * 2384278 * 2
def baseEnd_2384278 : Nat := 272062361764606163346647

theorem tailTrace_2384278 : CollatzResearch.WordTrace tailWord_2384278 prefixEnd_2384278 272062361764606163346647 := by
  unfold tailWord_2384278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5435110178510967694280093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 57974508570783655405654325 5435110178510967694280093)
  ·
    refine ⟨2038166316941612885355035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5435110178510967694280093 2038166316941612885355035)
    ·
      refine ⟨3057249475412419328032553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2038166316941612885355035 3057249475412419328032553)
      ·
        refine ⟨2292937106559314496024415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3057249475412419328032553 2292937106559314496024415)
        ·
          refine ⟨3439405659838971744036623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2292937106559314496024415 3439405659838971744036623)
          ·
            refine ⟨5159108489758457616054935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3439405659838971744036623 5159108489758457616054935)
            ·
              refine ⟨7738662734637686424082403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159108489758457616054935 7738662734637686424082403)
              ·
                refine ⟨11607994101956529636123605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7738662734637686424082403 11607994101956529636123605)
                ·
                  refine ⟨272062361764606163346647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11607994101956529636123605 272062361764606163346647)
                  ·
                    rfl

theorem cell22_2384278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_2384278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384278 prefixEnd_2384278 := by exact prefixLift 2384278
  have htrace : WordTrace (prefixWord ++ tailWord_2384278) baseStart_2384278 baseEnd_2384278 := by
    simpa [prefixWord, tailWord_2384278, baseEnd_2384278] using wordTrace_append hprefix tailTrace_2384278
  have hstable : (prefixWord ++ tailWord_2384278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384278).length < 2 ^ (prefixWord ++ tailWord_2384278).sum := by decide
  have hdescent : baseEnd_2384278 < baseStart_2384278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384300 : List Nat := [2, 2, 1, 1, 1, 1, 3, 11]
def baseStart_2384300 : Nat := 118140960795 + 2384300 * 2 ^ 59
def prefixEnd_2384300 : Nat := 4983230072969 + 3 ^ 40 * 2384300 * 2
def baseEnd_2384300 : Nat := 90688290704824196221097

theorem tailTrace_2384300 : CollatzResearch.WordTrace tailWord_2384300 prefixEnd_2384300 90688290704824196221097 := by
  unfold tailWord_2384300
  simp only [CollatzResearch.WordTrace]
  refine ⟨43481282631047890432891177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57975043508063853910521569 43481282631047890432891177)
  ·
    refine ⟨32610961973285917824668383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43481282631047890432891177 32610961973285917824668383)
    ·
      refine ⟨48916442959928876737002575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32610961973285917824668383 48916442959928876737002575)
      ·
        refine ⟨73374664439893315105503863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48916442959928876737002575 73374664439893315105503863)
        ·
          refine ⟨110061996659839972658255795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73374664439893315105503863 110061996659839972658255795)
          ·
            refine ⟨165092994989759958987383693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110061996659839972658255795 165092994989759958987383693)
            ·
              refine ⟨61909873121159984620268885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165092994989759958987383693 61909873121159984620268885)
              ·
                refine ⟨90688290704824196221097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 61909873121159984620268885 90688290704824196221097)
                ·
                  rfl

theorem cell22_2384300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 11].length) (baseStart_2384300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384300 prefixEnd_2384300 := by exact prefixLift 2384300
  have htrace : WordTrace (prefixWord ++ tailWord_2384300) baseStart_2384300 baseEnd_2384300 := by
    simpa [prefixWord, tailWord_2384300, baseEnd_2384300] using wordTrace_append hprefix tailTrace_2384300
  have hstable : (prefixWord ++ tailWord_2384300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384300).length < 2 ^ (prefixWord ++ tailWord_2384300).sum := by decide
  have hdescent : baseEnd_2384300 < baseStart_2384300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384317 : List Nat := [1, 4, 1, 2, 2, 3, 1, 8]
def baseStart_2384317 : Nat := 118140960795 + 2384317 * 2 ^ 59
def prefixEnd_2384317 : Nat := 4983230072969 + 3 ^ 40 * 2384317 * 2
def baseEnd_2384317 : Nat := 90688937310092820923869

theorem tailTrace_2384317 : CollatzResearch.WordTrace tailWord_2384317 prefixEnd_2384317 90688937310092820923869 := by
  unfold tailWord_2384317
  simp only [CollatzResearch.WordTrace]
  refine ⟨86963185303034192769151205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57975456868689461846100803 86963185303034192769151205)
  ·
    refine ⟨16305597244318911144215851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 86963185303034192769151205 16305597244318911144215851)
    ·
      refine ⟨24458395866478366716323777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16305597244318911144215851 24458395866478366716323777)
      ·
        refine ⟨18343796899858775037242833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24458395866478366716323777 18343796899858775037242833)
        ·
          refine ⟨13757847674894081277932125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18343796899858775037242833 13757847674894081277932125)
          ·
            refine ⟨5159192878085280479224547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13757847674894081277932125 5159192878085280479224547)
            ·
              refine ⟨7738789317127920718836821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5159192878085280479224547 7738789317127920718836821)
              ·
                refine ⟨90688937310092820923869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7738789317127920718836821 90688937310092820923869)
                ·
                  rfl

theorem cell22_2384317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 8].length) (baseStart_2384317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384317 prefixEnd_2384317 := by exact prefixLift 2384317
  have htrace : WordTrace (prefixWord ++ tailWord_2384317) baseStart_2384317 baseEnd_2384317 := by
    simpa [prefixWord, tailWord_2384317, baseEnd_2384317] using wordTrace_append hprefix tailTrace_2384317
  have hstable : (prefixWord ++ tailWord_2384317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384317).length < 2 ^ (prefixWord ++ tailWord_2384317).sum := by decide
  have hdescent : baseEnd_2384317 < baseStart_2384317 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384355 : List Nat := [1, 1, 1, 6, 4, 1, 2, 1, 2, 3]
def baseStart_2384355 : Nat := 118140960795 + 2384355 * 2 ^ 59
def prefixEnd_2384355 : Nat := 4983230072969 + 3 ^ 40 * 2384355 * 2
def baseEnd_2384355 : Nat := 816213443967415955864705

theorem tailTrace_2384355 : CollatzResearch.WordTrace tailWord_2384355 prefixEnd_2384355 816213443967415955864705 := by
  unfold tailWord_2384355
  simp only [CollatzResearch.WordTrace]
  refine ⟨86964571276896525259034519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57976380851264350172689679 86964571276896525259034519)
  ·
    refine ⟨130446856915344787888551779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86964571276896525259034519 130446856915344787888551779)
    ·
      refine ⟨195670285373017181832827669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130446856915344787888551779 195670285373017181832827669)
      ·
        refine ⟨9172044626860180398413797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 195670285373017181832827669 9172044626860180398413797)
        ·
          refine ⟨1719758367536283824702587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9172044626860180398413797 1719758367536283824702587)
          ·
            refine ⟨2579637551304425737053881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1719758367536283824702587 2579637551304425737053881)
            ·
              refine ⟨1934728163478319302790411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2579637551304425737053881 1934728163478319302790411)
              ·
                refine ⟨2902092245217478954185617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934728163478319302790411 2902092245217478954185617)
                ·
                  refine ⟨2176569183913109215639213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2902092245217478954185617 2176569183913109215639213)
                  ·
                    refine ⟨816213443967415955864705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2176569183913109215639213 816213443967415955864705)
                    ·
                      rfl

theorem cell22_2384355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 4, 1, 2, 1, 2, 3].length) (baseStart_2384355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384355 prefixEnd_2384355 := by exact prefixLift 2384355
  have htrace : WordTrace (prefixWord ++ tailWord_2384355) baseStart_2384355 baseEnd_2384355 := by
    simpa [prefixWord, tailWord_2384355, baseEnd_2384355] using wordTrace_append hprefix tailTrace_2384355
  have hstable : (prefixWord ++ tailWord_2384355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384355).length < 2 ^ (prefixWord ++ tailWord_2384355).sum := by decide
  have hdescent : baseEnd_2384355 < baseStart_2384355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384424 : List Nat := [2, 1, 5, 2, 1, 1, 1, 1, 8]
def baseStart_2384424 : Nat := 118140960795 + 2384424 * 2 ^ 59
def prefixEnd_2384424 : Nat := 4983230072969 + 3 ^ 40 * 2384424 * 2
def baseEnd_2384424 : Nat := 272079021359174258629831

theorem tailTrace_2384424 : CollatzResearch.WordTrace tailWord_2384424 prefixEnd_2384424 272079021359174258629831 := by
  unfold tailWord_2384424
  simp only [CollatzResearch.WordTrace]
  refine ⟨43483543956823275021648163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57978058609097700028864217 43483543956823275021648163)
  ·
    refine ⟨65225315935234912532472245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43483543956823275021648163 65225315935234912532472245)
    ·
      refine ⟨6114873368928273049919273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65225315935234912532472245 6114873368928273049919273)
      ·
        refine ⟨4586155026696204787439455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6114873368928273049919273 4586155026696204787439455)
        ·
          refine ⟨6879232540044307181159183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4586155026696204787439455 6879232540044307181159183)
          ·
            refine ⟨10318848810066460771738775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6879232540044307181159183 10318848810066460771738775)
            ·
              refine ⟨15478273215099691157608163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10318848810066460771738775 15478273215099691157608163)
              ·
                refine ⟨23217409822649536736412245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15478273215099691157608163 23217409822649536736412245)
                ·
                  refine ⟨272079021359174258629831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23217409822649536736412245 272079021359174258629831)
                  ·
                    rfl

theorem cell22_2384424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 1, 8].length) (baseStart_2384424 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384424 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384424 prefixEnd_2384424 := by exact prefixLift 2384424
  have htrace : WordTrace (prefixWord ++ tailWord_2384424) baseStart_2384424 baseEnd_2384424 := by
    simpa [prefixWord, tailWord_2384424, baseEnd_2384424] using wordTrace_append hprefix tailTrace_2384424
  have hstable : (prefixWord ++ tailWord_2384424).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384424).length < 2 ^ (prefixWord ++ tailWord_2384424).sum := by decide
  have hdescent : baseEnd_2384424 < baseStart_2384424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384439 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 4, 3]
def baseStart_2384439 : Nat := 118140960795 + 2384439 * 2 ^ 59
def prefixEnd_2384439 : Nat := 4983230072969 + 3 ^ 40 * 2384439 * 2
def baseEnd_2384439 : Nat := 816242198884067736764447

theorem tailTrace_2384439 : CollatzResearch.WordTrace tailWord_2384439 prefixEnd_2384439 816242198884067736764447 := by
  unfold tailWord_2384439
  simp only [CollatzResearch.WordTrace]
  refine ⟨86967635008592207605092371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57978423339061471736728247 86967635008592207605092371)
  ·
    refine ⟨130451452512888311407638557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86967635008592207605092371 130451452512888311407638557)
    ·
      refine ⟨48919294692333116777864459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130451452512888311407638557 48919294692333116777864459)
      ·
        refine ⟨73378942038499675166796689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48919294692333116777864459 73378942038499675166796689)
        ·
          refine ⟨55034206528874756375097517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73378942038499675166796689 55034206528874756375097517)
          ·
            refine ⟨20637827448328033640661569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55034206528874756375097517 20637827448328033640661569)
            ·
              refine ⟨15478370586246025230496177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20637827448328033640661569 15478370586246025230496177)
              ·
                refine ⟨11608777939684518922872133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15478370586246025230496177 11608777939684518922872133)
                ·
                  refine ⟨2176645863690847298038525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11608777939684518922872133 2176645863690847298038525)
                  ·
                    refine ⟨816242198884067736764447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2176645863690847298038525 816242198884067736764447)
                    ·
                      rfl

theorem cell22_2384439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_2384439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384439 prefixEnd_2384439 := by exact prefixLift 2384439
  have htrace : WordTrace (prefixWord ++ tailWord_2384439) baseStart_2384439 baseEnd_2384439 := by
    simpa [prefixWord, tailWord_2384439, baseEnd_2384439] using wordTrace_append hprefix tailTrace_2384439
  have hstable : (prefixWord ++ tailWord_2384439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384439).length < 2 ^ (prefixWord ++ tailWord_2384439).sum := by decide
  have hdescent : baseEnd_2384439 < baseStart_2384439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384441 : List Nat := [1, 2, 1, 5, 1, 1, 4, 3, 4]
def baseStart_2384441 : Nat := 118140960795 + 2384441 * 2 ^ 59
def prefixEnd_2384441 : Nat := 4983230072969 + 3 ^ 40 * 2384441 * 2
def baseEnd_2384441 : Nat := 272080961174980132738147

theorem tailTrace_2384441 : CollatzResearch.WordTrace tailWord_2384441 prefixEnd_2384441 272080961174980132738147 := by
  unfold tailWord_2384441
  simp only [CollatzResearch.WordTrace]
  refine ⟨86967707954584961946665177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57978471969723307964443451 86967707954584961946665177)
  ·
    refine ⟨65225780965938721459998883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86967707954584961946665177 65225780965938721459998883)
    ·
      refine ⟨97838671448908082189998325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65225780965938721459998883 97838671448908082189998325)
      ·
        refine ⟨9172375448335132705312343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97838671448908082189998325 9172375448335132705312343)
        ·
          refine ⟨13758563172502699057968515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9172375448335132705312343 13758563172502699057968515)
          ·
            refine ⟨20637844758754048586952773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13758563172502699057968515 20637844758754048586952773)
            ·
              refine ⟨3869595892266384110053645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20637844758754048586952773 3869595892266384110053645)
              ·
                refine ⟨1451098459599894041270117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3869595892266384110053645 1451098459599894041270117)
                ·
                  refine ⟨272080961174980132738147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1451098459599894041270117 272080961174980132738147)
                  ·
                    rfl

theorem cell22_2384441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 3, 4].length) (baseStart_2384441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384441 prefixEnd_2384441 := by exact prefixLift 2384441
  have htrace : WordTrace (prefixWord ++ tailWord_2384441) baseStart_2384441 baseEnd_2384441 := by
    simpa [prefixWord, tailWord_2384441, baseEnd_2384441] using wordTrace_append hprefix tailTrace_2384441
  have hstable : (prefixWord ++ tailWord_2384441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384441).length < 2 ^ (prefixWord ++ tailWord_2384441).sum := by decide
  have hdescent : baseEnd_2384441 < baseStart_2384441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384634 : List Nat := [3, 1, 1, 1, 1, 3, 2, 1, 1, 8]
def baseStart_2384634 : Nat := 118140960795 + 2384634 * 2 ^ 59
def prefixEnd_2384634 : Nat := 4983230072969 + 3 ^ 40 * 2384634 * 2
def baseEnd_2384634 : Nat := 816308951369152228138849

theorem tailTrace_2384634 : CollatzResearch.WordTrace tailWord_2384634 prefixEnd_2384634 816308951369152228138849 := by
  unfold tailWord_2384634
  simp only [CollatzResearch.WordTrace]
  refine ⟨21743686810721438977110239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57983164828590503938960637 21743686810721438977110239)
  ·
    refine ⟨32615530216082158465665359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21743686810721438977110239 32615530216082158465665359)
    ·
      refine ⟨48923295324123237698498039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32615530216082158465665359 48923295324123237698498039)
      ·
        refine ⟨73384942986184856547747059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48923295324123237698498039 73384942986184856547747059)
        ·
          refine ⟨110077414479277284821620589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73384942986184856547747059 110077414479277284821620589)
          ·
            refine ⟨41279030429728981808107721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110077414479277284821620589 41279030429728981808107721)
            ·
              refine ⟨30959272822296736356080791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41279030429728981808107721 30959272822296736356080791)
              ·
                refine ⟨46438909233445104534121187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30959272822296736356080791 46438909233445104534121187)
                ·
                  refine ⟨69658363850167656801181781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 46438909233445104534121187 69658363850167656801181781)
                  ·
                    refine ⟨816308951369152228138849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 69658363850167656801181781 816308951369152228138849)
                    ·
                      rfl

theorem cell22_2384634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 1, 1, 8].length) (baseStart_2384634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384634 prefixEnd_2384634 := by exact prefixLift 2384634
  have htrace : WordTrace (prefixWord ++ tailWord_2384634) baseStart_2384634 baseEnd_2384634 := by
    simpa [prefixWord, tailWord_2384634, baseEnd_2384634] using wordTrace_append hprefix tailTrace_2384634
  have hstable : (prefixWord ++ tailWord_2384634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384634).length < 2 ^ (prefixWord ++ tailWord_2384634).sum := by decide
  have hdescent : baseEnd_2384634 < baseStart_2384634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384642 : List Nat := [3, 4, 1, 1, 1, 3, 3, 1, 2, 3]
def baseStart_2384642 : Nat := 118140960795 + 2384642 * 2 ^ 59
def prefixEnd_2384642 : Nat := 4983230072969 + 3 ^ 40 * 2384642 * 2
def baseEnd_2384642 : Nat := 816311689932642873938825

theorem tailTrace_2384642 : CollatzResearch.WordTrace tailWord_2384642 prefixEnd_2384642 816311689932642873938825 := by
  unfold tailWord_2384642
  simp only [CollatzResearch.WordTrace]
  refine ⟨21743759756714193318683045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57983359351237848849821453 21743759756714193318683045)
  ·
    refine ⟨4076954954383911247253071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21743759756714193318683045 4076954954383911247253071)
    ·
      refine ⟨6115432431575866870879607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4076954954383911247253071 6115432431575866870879607)
      ·
        refine ⟨9173148647363800306319411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6115432431575866870879607 9173148647363800306319411)
        ·
          refine ⟨13759722971045700459479117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9173148647363800306319411 13759722971045700459479117)
          ·
            refine ⟨5159896114142137672304669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13759722971045700459479117 5159896114142137672304669)
            ·
              refine ⟨1934961042803301627114251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5159896114142137672304669 1934961042803301627114251)
              ·
                refine ⟨2902441564204952440671377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1934961042803301627114251 2902441564204952440671377)
                ·
                  refine ⟨2176831173153714330503533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2902441564204952440671377 2176831173153714330503533)
                  ·
                    refine ⟨816311689932642873938825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2176831173153714330503533 816311689932642873938825)
                    ·
                      rfl

theorem cell22_2384642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 3, 1, 2, 3].length) (baseStart_2384642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384642 prefixEnd_2384642 := by exact prefixLift 2384642
  have htrace : WordTrace (prefixWord ++ tailWord_2384642) baseStart_2384642 baseEnd_2384642 := by
    simpa [prefixWord, tailWord_2384642, baseEnd_2384642] using wordTrace_append hprefix tailTrace_2384642
  have hstable : (prefixWord ++ tailWord_2384642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384642).length < 2 ^ (prefixWord ++ tailWord_2384642).sum := by decide
  have hdescent : baseEnd_2384642 < baseStart_2384642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384696 : List Nat := [2, 1, 2, 1, 3, 2, 2, 2, 3, 4]
def baseStart_2384696 : Nat := 118140960795 + 2384696 * 2 ^ 59
def prefixEnd_2384696 : Nat := 4983230072969 + 3 ^ 40 * 2384696 * 2
def baseEnd_2384696 : Nat := 816330175236204733088659

theorem tailTrace_2384696 : CollatzResearch.WordTrace tailWord_2384696 prefixEnd_2384696 816330175236204733088659 := by
  unfold tailWord_2384696
  simp only [CollatzResearch.WordTrace]
  refine ⟨43488504284330570248598971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57984672379107426998131961 43488504284330570248598971)
  ·
    refine ⟨65232756426495855372898457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43488504284330570248598971 65232756426495855372898457)
    ·
      refine ⟨48924567319871891529673843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65232756426495855372898457 48924567319871891529673843)
      ·
        refine ⟨73386850979807837294510765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48924567319871891529673843 73386850979807837294510765)
        ·
          refine ⟨27520069117427938985441537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73386850979807837294510765 27520069117427938985441537)
          ·
            refine ⟨20640051838070954239081153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27520069117427938985441537 20640051838070954239081153)
            ·
              refine ⟨15480038878553215679310865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20640051838070954239081153 15480038878553215679310865)
              ·
                refine ⟨11610029158914911759483149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15480038878553215679310865 11610029158914911759483149)
                ·
                  refine ⟨4353760934593091909806181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11610029158914911759483149 4353760934593091909806181)
                  ·
                    refine ⟨816330175236204733088659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4353760934593091909806181 816330175236204733088659)
                    ·
                      rfl

theorem cell22_2384696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_2384696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384696 prefixEnd_2384696 := by exact prefixLift 2384696
  have htrace : WordTrace (prefixWord ++ tailWord_2384696) baseStart_2384696 baseEnd_2384696 := by
    simpa [prefixWord, tailWord_2384696, baseEnd_2384696] using wordTrace_append hprefix tailTrace_2384696
  have hstable : (prefixWord ++ tailWord_2384696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384696).length < 2 ^ (prefixWord ++ tailWord_2384696).sum := by decide
  have hdescent : baseEnd_2384696 < baseStart_2384696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384713 : List Nat := [1, 2, 1, 1, 2, 5, 3, 2, 1, 4]
def baseStart_2384713 : Nat := 118140960795 + 2384713 * 2 ^ 59
def prefixEnd_2384713 : Nat := 4983230072969 + 3 ^ 40 * 2384713 * 2
def baseEnd_2384713 : Nat := 816335994683622355413607

theorem tailTrace_2384713 : CollatzResearch.WordTrace tailWord_2384713 prefixEnd_2384713 816335994683622355413607 := by
  unfold tailWord_2384713
  simp only [CollatzResearch.WordTrace]
  refine ⟨86977628609599552400566793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57985085739733034933711195 86977628609599552400566793)
  ·
    refine ⟨65233221457199664300425095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86977628609599552400566793 65233221457199664300425095)
    ·
      refine ⟨97849832185799496450637643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65233221457199664300425095 97849832185799496450637643)
      ·
        refine ⟨146774748278699244675956465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97849832185799496450637643 146774748278699244675956465)
        ·
          refine ⟨110081061209024433506967349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146774748278699244675956465 110081061209024433506967349)
          ·
            refine ⟨10320099488346040641278189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110081061209024433506967349 10320099488346040641278189)
            ·
              refine ⟨3870037308129765240479321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10320099488346040641278189 3870037308129765240479321)
              ·
                refine ⟨2902527981097323930359491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3870037308129765240479321 2902527981097323930359491)
                ·
                  refine ⟨4353791971645985895539237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902527981097323930359491 4353791971645985895539237)
                  ·
                    refine ⟨816335994683622355413607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4353791971645985895539237 816335994683622355413607)
                    ·
                      rfl

theorem cell22_2384713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 3, 2, 1, 4].length) (baseStart_2384713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384713 prefixEnd_2384713 := by exact prefixLift 2384713
  have htrace : WordTrace (prefixWord ++ tailWord_2384713) baseStart_2384713 baseEnd_2384713 := by
    simpa [prefixWord, tailWord_2384713, baseEnd_2384713] using wordTrace_append hprefix tailTrace_2384713
  have hstable : (prefixWord ++ tailWord_2384713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384713).length < 2 ^ (prefixWord ++ tailWord_2384713).sum := by decide
  have hdescent : baseEnd_2384713 < baseStart_2384713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384730 : List Nat := [3, 1, 1, 2, 1, 5, 3, 1, 1, 4]
def baseStart_2384730 : Nat := 118140960795 + 2384730 * 2 ^ 59
def prefixEnd_2384730 : Nat := 4983230072969 + 3 ^ 40 * 2384730 * 2
def baseEnd_2384730 : Nat := 816341814131039977738555

theorem tailTrace_2384730 : CollatzResearch.WordTrace tailWord_2384730 prefixEnd_2384730 816341814131039977738555 := by
  unfold tailWord_2384730
  simp only [CollatzResearch.WordTrace]
  refine ⟨21744562162634491075983911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57985499100358642869290429 21744562162634491075983911)
  ·
    refine ⟨32616843243951736613975867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21744562162634491075983911 32616843243951736613975867)
    ·
      refine ⟨48925264865927604920963801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32616843243951736613975867 48925264865927604920963801)
      ·
        refine ⟨36693948649445703690722851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48925264865927604920963801 36693948649445703690722851)
        ·
          refine ⟨55040922974168555536084277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36693948649445703690722851 55040922974168555536084277)
          ·
            refine ⟨5160086528828302081507901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55040922974168555536084277 5160086528828302081507901)
            ·
              refine ⟨1935032448310613280565463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5160086528828302081507901 1935032448310613280565463)
              ·
                refine ⟨2902548672465919920848195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935032448310613280565463 2902548672465919920848195)
                ·
                  refine ⟨4353823008698879881272293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2902548672465919920848195 4353823008698879881272293)
                  ·
                    refine ⟨816341814131039977738555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4353823008698879881272293 816341814131039977738555)
                    ·
                      rfl

theorem cell22_2384730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 3, 1, 1, 4].length) (baseStart_2384730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384730 prefixEnd_2384730 := by exact prefixLift 2384730
  have htrace : WordTrace (prefixWord ++ tailWord_2384730) baseStart_2384730 baseEnd_2384730 := by
    simpa [prefixWord, tailWord_2384730, baseEnd_2384730] using wordTrace_append hprefix tailTrace_2384730
  have hstable : (prefixWord ++ tailWord_2384730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384730).length < 2 ^ (prefixWord ++ tailWord_2384730).sum := by decide
  have hdescent : baseEnd_2384730 < baseStart_2384730 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384773 : List Nat := [1, 3, 1, 1, 3, 4, 3, 6]
def baseStart_2384773 : Nat := 118140960795 + 2384773 * 2 ^ 59
def prefixEnd_2384773 : Nat := 4983230072969 + 3 ^ 40 * 2384773 * 2
def baseEnd_2384773 : Nat := 90706281545533577657047

theorem tailTrace_2384773 : CollatzResearch.WordTrace tailWord_2384773 prefixEnd_2384773 90706281545533577657047 := by
  unfold tailWord_2384773
  simp only [CollatzResearch.WordTrace]
  refine ⟨86979816989382182647750973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57986544659588121765167315 86979816989382182647750973)
  ·
    refine ⟨32617431371018318492906615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86979816989382182647750973 32617431371018318492906615)
    ·
      refine ⟨48926147056527477739359923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32617431371018318492906615 48926147056527477739359923)
      ·
        refine ⟨73389220584791216609039885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48926147056527477739359923 73389220584791216609039885)
        ·
          refine ⟨27520957719296706228389957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73389220584791216609039885 27520957719296706228389957)
          ·
            refine ⟨5160179572368132417823117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27520957719296706228389957 5160179572368132417823117)
            ·
              refine ⟨1935067339638049656683669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5160179572368132417823117 1935067339638049656683669)
              ·
                refine ⟨90706281545533577657047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1935067339638049656683669 90706281545533577657047)
                ·
                  rfl

theorem cell22_2384773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 3, 6].length) (baseStart_2384773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384773 prefixEnd_2384773 := by exact prefixLift 2384773
  have htrace : WordTrace (prefixWord ++ tailWord_2384773) baseStart_2384773 baseEnd_2384773 := by
    simpa [prefixWord, tailWord_2384773, baseEnd_2384773] using wordTrace_append hprefix tailTrace_2384773
  have hstable : (prefixWord ++ tailWord_2384773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384773).length < 2 ^ (prefixWord ++ tailWord_2384773).sum := by decide
  have hdescent : baseEnd_2384773 < baseStart_2384773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384775 : List Nat := [1, 1, 4, 2, 3, 3, 1, 1, 2, 4]
def baseStart_2384775 : Nat := 118140960795 + 2384775 * 2 ^ 59
def prefixEnd_2384775 : Nat := 4983230072969 + 3 ^ 40 * 2384775 * 2
def baseEnd_2384775 : Nat := 816357218550674860363417

theorem tailTrace_2384775 : CollatzResearch.WordTrace tailWord_2384775 prefixEnd_2384775 816357218550674860363417 := by
  unfold tailWord_2384775
  simp only [CollatzResearch.WordTrace]
  refine ⟨86979889935374936989323779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57986593290249957992882519 86979889935374936989323779)
  ·
    refine ⟨130469834903062405483985669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86979889935374936989323779 130469834903062405483985669)
    ·
      refine ⟨24463094044324201028247313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130469834903062405483985669 24463094044324201028247313)
      ·
        refine ⟨18347320533243150771185485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24463094044324201028247313 18347320533243150771185485)
        ·
          refine ⟨6880245199966181539194557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18347320533243150771185485 6880245199966181539194557)
          ·
            refine ⟨2580091949987318077197959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6880245199966181539194557 2580091949987318077197959)
            ·
              refine ⟨3870137924980977115796939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580091949987318077197959 3870137924980977115796939)
              ·
                refine ⟨5805206887471465673695409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3870137924980977115796939 5805206887471465673695409)
                ·
                  refine ⟨4353905165603599255271557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5805206887471465673695409 4353905165603599255271557)
                  ·
                    refine ⟨816357218550674860363417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4353905165603599255271557 816357218550674860363417)
                    ·
                      rfl

theorem cell22_2384775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_2384775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384775 prefixEnd_2384775 := by exact prefixLift 2384775
  have htrace : WordTrace (prefixWord ++ tailWord_2384775) baseStart_2384775 baseEnd_2384775 := by
    simpa [prefixWord, tailWord_2384775, baseEnd_2384775] using wordTrace_append hprefix tailTrace_2384775
  have hstable : (prefixWord ++ tailWord_2384775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384775).length < 2 ^ (prefixWord ++ tailWord_2384775).sum := by decide
  have hdescent : baseEnd_2384775 < baseStart_2384775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384794 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 2, 3]
def baseStart_2384794 : Nat := 118140960795 + 2384794 * 2 ^ 59
def prefixEnd_2384794 : Nat := 4983230072969 + 3 ^ 40 * 2384794 * 2
def baseEnd_2384794 : Nat := 816363722638965144138359

theorem tailTrace_2384794 : CollatzResearch.WordTrace tailWord_2384794 prefixEnd_2384794 816363722638965144138359 := by
  unfold tailWord_2384794
  simp only [CollatzResearch.WordTrace]
  refine ⟨21745145730576525808566359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57987055281537402156176957 21745145730576525808566359)
  ·
    refine ⟨32617718595864788712849539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21745145730576525808566359 32617718595864788712849539)
    ·
      refine ⟨48926577893797183069274309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32617718595864788712849539 48926577893797183069274309)
      ·
        refine ⟨9173733355086971825488933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48926577893797183069274309 9173733355086971825488933)
        ·
          refine ⟨1720075004078807217279175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9173733355086971825488933 1720075004078807217279175)
          ·
            refine ⟨2580112506118210825918763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720075004078807217279175 2580112506118210825918763)
            ·
              refine ⟨3870168759177316238878145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580112506118210825918763 3870168759177316238878145)
              ·
                refine ⟨2902626569382987179158609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3870168759177316238878145 2902626569382987179158609)
                ·
                  refine ⟨2176969927037240384368957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2902626569382987179158609 2176969927037240384368957)
                  ·
                    refine ⟨816363722638965144138359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2176969927037240384368957 816363722638965144138359)
                    ·
                      rfl

theorem cell22_2384794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 2, 3].length) (baseStart_2384794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384794 prefixEnd_2384794 := by exact prefixLift 2384794
  have htrace : WordTrace (prefixWord ++ tailWord_2384794) baseStart_2384794 baseEnd_2384794 := by
    simpa [prefixWord, tailWord_2384794, baseEnd_2384794] using wordTrace_append hprefix tailTrace_2384794
  have hstable : (prefixWord ++ tailWord_2384794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384794).length < 2 ^ (prefixWord ++ tailWord_2384794).sum := by decide
  have hdescent : baseEnd_2384794 < baseStart_2384794 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384869 : List Nat := [1, 3, 1, 6, 1, 2, 2, 1, 5]
def baseStart_2384869 : Nat := 118140960795 + 2384869 * 2 ^ 59
def prefixEnd_2384869 : Nat := 4983230072969 + 3 ^ 40 * 2384869 * 2
def baseEnd_2384869 : Nat := 272129798890563316171043

theorem tailTrace_2384869 : CollatzResearch.WordTrace tailWord_2384869 prefixEnd_2384869 272129798890563316171043 := by
  unfold tailWord_2384869
  simp only [CollatzResearch.WordTrace]
  refine ⟨86983318397034391043245661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57988878931356260695497107 86983318397034391043245661)
  ·
    refine ⟨32618744398887896641217123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86983318397034391043245661 32618744398887896641217123)
    ·
      refine ⟨48928116598331844961825685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32618744398887896641217123 48928116598331844961825685)
      ·
        refine ⟨2293505465546805232585579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 48928116598331844961825685 2293505465546805232585579)
        ·
          refine ⟨3440258198320207848878369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2293505465546805232585579 3440258198320207848878369)
          ·
            refine ⟨2580193648740155886658777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3440258198320207848878369 2580193648740155886658777)
            ·
              refine ⟨1935145236555116914994083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2580193648740155886658777 1935145236555116914994083)
              ·
                refine ⟨2902717854832675372491125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935145236555116914994083 2902717854832675372491125)
                ·
                  refine ⟨272129798890563316171043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2902717854832675372491125 272129798890563316171043)
                  ·
                    rfl

theorem cell22_2384869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 2, 1, 5].length) (baseStart_2384869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384869 prefixEnd_2384869 := by exact prefixLift 2384869
  have htrace : WordTrace (prefixWord ++ tailWord_2384869) baseStart_2384869 baseEnd_2384869 := by
    simpa [prefixWord, tailWord_2384869, baseEnd_2384869] using wordTrace_append hprefix tailTrace_2384869
  have hstable : (prefixWord ++ tailWord_2384869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384869).length < 2 ^ (prefixWord ++ tailWord_2384869).sum := by decide
  have hdescent : baseEnd_2384869 < baseStart_2384869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384882 : List Nat := [3, 2, 1, 5, 1, 1, 1, 1, 3, 4]
def baseStart_2384882 : Nat := 118140960795 + 2384882 * 2 ^ 59
def prefixEnd_2384882 : Nat := 4983230072969 + 3 ^ 40 * 2384882 * 2
def baseEnd_2384882 : Nat := 816393846837362247938089

theorem tailTrace_2384882 : CollatzResearch.WordTrace tailWord_2384882 prefixEnd_2384882 816393846837362247938089 := by
  unfold tailWord_2384882
  simp only [CollatzResearch.WordTrace]
  refine ⟨21745948136496823565867225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57989195030658196175645933 21745948136496823565867225)
  ·
    refine ⟨16309461102372617674400419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21745948136496823565867225 16309461102372617674400419)
    ·
      refine ⟨24464191653558926511600629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16309461102372617674400419 24464191653558926511600629)
      ·
        refine ⟨2293517967521149360462559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 24464191653558926511600629 2293517967521149360462559)
        ·
          refine ⟨3440276951281724040693839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2293517967521149360462559 3440276951281724040693839)
          ·
            refine ⟨5160415426922586061040759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3440276951281724040693839 5160415426922586061040759)
            ·
              refine ⟨7740623140383879091561139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5160415426922586061040759 7740623140383879091561139)
              ·
                refine ⟨11610934710575818637341709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7740623140383879091561139 11610934710575818637341709)
                ·
                  refine ⟨4354100516465931989003141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11610934710575818637341709 4354100516465931989003141)
                  ·
                    refine ⟨816393846837362247938089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4354100516465931989003141 816393846837362247938089)
                    ·
                      rfl

theorem cell22_2384882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_2384882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384882 prefixEnd_2384882 := by exact prefixLift 2384882
  have htrace : WordTrace (prefixWord ++ tailWord_2384882) baseStart_2384882 baseEnd_2384882 := by
    simpa [prefixWord, tailWord_2384882, baseEnd_2384882] using wordTrace_append hprefix tailTrace_2384882
  have hstable : (prefixWord ++ tailWord_2384882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384882).length < 2 ^ (prefixWord ++ tailWord_2384882).sum := by decide
  have hdescent : baseEnd_2384882 < baseStart_2384882 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384910 : List Nat := [4, 1, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_2384910 : Nat := 118140960795 + 2384910 * 2 ^ 59
def prefixEnd_2384910 : Nat := 4983230072969 + 3 ^ 40 * 2384910 * 2
def baseEnd_2384910 : Nat := 816403431809579508238003

theorem tailTrace_2384910 : CollatzResearch.WordTrace tailWord_2384910 prefixEnd_2384910 816403431809579508238003 := by
  unfold tailWord_2384910
  simp only [CollatzResearch.WordTrace]
  refine ⟨10873101723735731880686023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 57989875859923903363658789 10873101723735731880686023)
  ·
    refine ⟨16309652585603597821029035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10873101723735731880686023 16309652585603597821029035)
    ·
      refine ⟨24464478878405396731543553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16309652585603597821029035 24464478878405396731543553)
      ·
        refine ⟨18348359158804047548657665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24464478878405396731543553 18348359158804047548657665)
        ·
          refine ⟨13761269369103035661493249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18348359158804047548657665 13761269369103035661493249)
          ·
            refine ⟨10320952026827276746119937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13761269369103035661493249 10320952026827276746119937)
            ·
              refine ⟨7740714020120457559589953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10320952026827276746119937 7740714020120457559589953)
              ·
                refine ⟨5805535515090343169692465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7740714020120457559589953 5805535515090343169692465)
                ·
                  refine ⟨4354151636317757377269349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5805535515090343169692465 4354151636317757377269349)
                  ·
                    refine ⟨816403431809579508238003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4354151636317757377269349 816403431809579508238003)
                    ·
                      rfl

theorem cell22_2384910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_2384910 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384910 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384910 prefixEnd_2384910 := by exact prefixLift 2384910
  have htrace : WordTrace (prefixWord ++ tailWord_2384910) baseStart_2384910 baseEnd_2384910 := by
    simpa [prefixWord, tailWord_2384910, baseEnd_2384910] using wordTrace_append hprefix tailTrace_2384910
  have hstable : (prefixWord ++ tailWord_2384910).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384910).length < 2 ^ (prefixWord ++ tailWord_2384910).sum := by decide
  have hdescent : baseEnd_2384910 < baseStart_2384910 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384940 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 3, 3]
def baseStart_2384940 : Nat := 118140960795 + 2384940 * 2 ^ 59
def prefixEnd_2384940 : Nat := 4983230072969 + 3 ^ 40 * 2384940 * 2
def baseEnd_2384940 : Nat := 816413701422669429987911

theorem tailTrace_2384940 : CollatzResearch.WordTrace tailWord_2384940 prefixEnd_2384940 816413701422669429987911 := by
  unfold tailWord_2384940
  simp only [CollatzResearch.WordTrace]
  refine ⟨43492953989888585084540137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57990605319851446779386849 43492953989888585084540137)
  ·
    refine ⟨32619715492416438813405103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43492953989888585084540137 32619715492416438813405103)
    ·
      refine ⟨48929573238624658220107655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32619715492416438813405103 48929573238624658220107655)
      ·
        refine ⟨73394359857936987330161483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48929573238624658220107655 73394359857936987330161483)
        ·
          refine ⟨110091539786905480995242225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73394359857936987330161483 110091539786905480995242225)
          ·
            refine ⟨82568654840179110746431669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110091539786905480995242225 82568654840179110746431669)
            ·
              refine ⟨7740811391266791632477969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 82568654840179110746431669 7740811391266791632477969)
              ·
                refine ⟨5805608543450093724358477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7740811391266791632477969 5805608543450093724358477)
                ·
                  refine ⟨2177103203793785146634429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5805608543450093724358477 2177103203793785146634429)
                  ·
                    refine ⟨816413701422669429987911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2177103203793785146634429 816413701422669429987911)
                    ·
                      rfl

theorem cell22_2384940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 3].length) (baseStart_2384940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384940 prefixEnd_2384940 := by exact prefixLift 2384940
  have htrace : WordTrace (prefixWord ++ tailWord_2384940) baseStart_2384940 baseEnd_2384940 := by
    simpa [prefixWord, tailWord_2384940, baseEnd_2384940] using wordTrace_append hprefix tailTrace_2384940
  have hstable : (prefixWord ++ tailWord_2384940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384940).length < 2 ^ (prefixWord ++ tailWord_2384940).sum := by decide
  have hdescent : baseEnd_2384940 < baseStart_2384940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384968 : List Nat := [2, 1, 3, 1, 1, 1, 3, 1, 4, 5]
def baseStart_2384968 : Nat := 118140960795 + 2384968 * 2 ^ 59
def prefixEnd_2384968 : Nat := 4983230072969 + 3 ^ 40 * 2384968 * 2
def baseEnd_2384968 : Nat := 816423286394886690287825

theorem tailTrace_2384968 : CollatzResearch.WordTrace tailWord_2384968 prefixEnd_2384968 816423286394886690287825 := by
  unfold tailWord_2384968
  simp only [CollatzResearch.WordTrace]
  refine ⟨43493464611837865475549779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57991286149117153967399705 43493464611837865475549779)
  ·
    refine ⟨65240196917756798213324669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43493464611837865475549779 65240196917756798213324669)
    ·
      refine ⟨24465073844158799329996751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65240196917756798213324669 24465073844158799329996751)
      ·
        refine ⟨36697610766238198994995127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24465073844158799329996751 36697610766238198994995127)
        ·
          refine ⟨55046416149357298492492691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36697610766238198994995127 55046416149357298492492691)
          ·
            refine ⟨82569624224035947738739037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55046416149357298492492691 82569624224035947738739037)
            ·
              refine ⟨30963609084013480402027139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 82569624224035947738739037 30963609084013480402027139)
              ·
                refine ⟨46445413626020220603040709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30963609084013480402027139 46445413626020220603040709)
                ·
                  refine ⟨8708515054878791363070133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 46445413626020220603040709 8708515054878791363070133)
                  ·
                    refine ⟨816423286394886690287825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8708515054878791363070133 816423286394886690287825)
                    ·
                      rfl

theorem cell22_2384968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_2384968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384968 prefixEnd_2384968 := by exact prefixLift 2384968
  have htrace : WordTrace (prefixWord ++ tailWord_2384968) baseStart_2384968 baseEnd_2384968 := by
    simpa [prefixWord, tailWord_2384968, baseEnd_2384968] using wordTrace_append hprefix tailTrace_2384968
  have hstable : (prefixWord ++ tailWord_2384968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384968).length < 2 ^ (prefixWord ++ tailWord_2384968).sum := by decide
  have hdescent : baseEnd_2384968 < baseStart_2384968 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2384970 : List Nat := [3, 1, 2, 1, 1, 2, 5, 2, 5]
def baseStart_2384970 : Nat := 118140960795 + 2384970 * 2 ^ 59
def prefixEnd_2384970 : Nat := 4983230072969 + 3 ^ 40 * 2384970 * 2
def baseEnd_2384970 : Nat := 272141323678586450579273

theorem tailTrace_2384970 : CollatzResearch.WordTrace tailWord_2384970 prefixEnd_2384970 272141323678586450579273 := by
  unfold tailWord_2384970
  simp only [CollatzResearch.WordTrace]
  refine ⟨21746750542417121323168091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 57991334779778990195114909 21746750542417121323168091)
  ·
    refine ⟨32620125813625681984752137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21746750542417121323168091 32620125813625681984752137)
    ·
      refine ⟨24465094360219261488564103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32620125813625681984752137 24465094360219261488564103)
      ·
        refine ⟨36697641540328892232846155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24465094360219261488564103 36697641540328892232846155)
        ·
          refine ⟨55046462310493338349269233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36697641540328892232846155 55046462310493338349269233)
          ·
            refine ⟨41284846732870003761951925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55046462310493338349269233 41284846732870003761951925)
            ·
              refine ⟨3870454381206562852682993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41284846732870003761951925 3870454381206562852682993)
              ·
                refine ⟨2902840785904922139512245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3870454381206562852682993 2902840785904922139512245)
                ·
                  refine ⟨272141323678586450579273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2902840785904922139512245 272141323678586450579273)
                  ·
                    rfl

theorem cell22_2384970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 5, 2, 5].length) (baseStart_2384970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2384970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2384970 prefixEnd_2384970 := by exact prefixLift 2384970
  have htrace : WordTrace (prefixWord ++ tailWord_2384970) baseStart_2384970 baseEnd_2384970 := by
    simpa [prefixWord, tailWord_2384970, baseEnd_2384970] using wordTrace_append hprefix tailTrace_2384970
  have hstable : (prefixWord ++ tailWord_2384970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2384970).length < 2 ^ (prefixWord ++ tailWord_2384970).sum := by decide
  have hdescent : baseEnd_2384970 < baseStart_2384970 := by decide
  rcases family_descends (prefixWord ++ tailWord_2384970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385043 : List Nat := [1, 1, 1, 2, 1, 2, 5, 9]
def baseStart_2385043 : Nat := 118140960795 + 2385043 * 2 ^ 59
def prefixEnd_2385043 : Nat := 4983230072969 + 3 ^ 40 * 2385043 * 2
def baseEnd_2385043 : Nat := 90716551158623499406955

theorem tailTrace_2385043 : CollatzResearch.WordTrace tailWord_2385043 prefixEnd_2385043 90716551158623499406955 := by
  unfold tailWord_2385043
  simp only [CollatzResearch.WordTrace]
  refine ⟨86989664698404018760079783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57993109798936012506719855 86989664698404018760079783)
  ·
    refine ⟨130484497047606028140119675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86989664698404018760079783 130484497047606028140119675)
    ·
      refine ⟨195726745571409042210179513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130484497047606028140119675 195726745571409042210179513)
      ·
        refine ⟨146795059178556781657634635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195726745571409042210179513 146795059178556781657634635)
        ·
          refine ⟨220192588767835172486451953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146795059178556781657634635 220192588767835172486451953)
          ·
            refine ⟨165144441575876379364838965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220192588767835172486451953 165144441575876379364838965)
            ·
              refine ⟨15482291397738410565453653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165144441575876379364838965 15482291397738410565453653)
              ·
                refine ⟨90716551158623499406955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15482291397738410565453653 90716551158623499406955)
                ·
                  rfl

theorem cell22_2385043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 9].length) (baseStart_2385043 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385043 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385043 prefixEnd_2385043 := by exact prefixLift 2385043
  have htrace : WordTrace (prefixWord ++ tailWord_2385043) baseStart_2385043 baseEnd_2385043 := by
    simpa [prefixWord, tailWord_2385043, baseEnd_2385043] using wordTrace_append hprefix tailTrace_2385043
  have hstable : (prefixWord ++ tailWord_2385043).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385043).length < 2 ^ (prefixWord ++ tailWord_2385043).sum := by decide
  have hdescent : baseEnd_2385043 < baseStart_2385043 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385060 : List Nat := [2, 3, 1, 2, 3, 1, 2, 8]
def baseStart_2385060 : Nat := 118140960795 + 2385060 * 2 ^ 59
def prefixEnd_2385060 : Nat := 4983230072969 + 3 ^ 40 * 2385060 * 2
def baseEnd_2385060 : Nat := 90717197763892124109727

theorem tailTrace_2385060 : CollatzResearch.WordTrace tailWord_2385060 prefixEnd_2385060 90717197763892124109727 := by
  unfold tailWord_2385060
  simp only [CollatzResearch.WordTrace]
  refine ⟨43495142369671215331724317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57993523159561620442299089 43495142369671215331724317)
  ·
    refine ⟨16310678388626705749396619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43495142369671215331724317 16310678388626705749396619)
    ·
      refine ⟨24466017582940058624094929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16310678388626705749396619 24466017582940058624094929)
      ·
        refine ⟨18349513187205043968071197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24466017582940058624094929 18349513187205043968071197)
        ·
          refine ⟨6881067445201891488026699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18349513187205043968071197 6881067445201891488026699)
          ·
            refine ⟨10321601167802837232040049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6881067445201891488026699 10321601167802837232040049)
            ·
              refine ⟨7741200875852127924030037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10321601167802837232040049 7741200875852127924030037)
              ·
                refine ⟨90717197763892124109727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7741200875852127924030037 90717197763892124109727)
                ·
                  rfl

theorem cell22_2385060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 8].length) (baseStart_2385060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385060 prefixEnd_2385060 := by exact prefixLift 2385060
  have htrace : WordTrace (prefixWord ++ tailWord_2385060) baseStart_2385060 baseEnd_2385060 := by
    simpa [prefixWord, tailWord_2385060, baseEnd_2385060] using wordTrace_append hprefix tailTrace_2385060
  have hstable : (prefixWord ++ tailWord_2385060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385060).length < 2 ^ (prefixWord ++ tailWord_2385060).sum := by decide
  have hdescent : baseEnd_2385060 < baseStart_2385060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385109 : List Nat := [1, 3, 2, 4, 1, 2, 1, 2, 3, 3]
def baseStart_2385109 : Nat := 118140960795 + 2385109 * 2 ^ 59
def prefixEnd_2385109 : Nat := 4983230072969 + 3 ^ 40 * 2385109 * 2
def baseEnd_2385109 : Nat := 816471553576409322512393

theorem tailTrace_2385109 : CollatzResearch.WordTrace tailWord_2385109 prefixEnd_2385109 816471553576409322512393 := by
  unfold tailWord_2385109
  simp only [CollatzResearch.WordTrace]
  refine ⟨86992071916164912031982381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57994714610776608021321587 86992071916164912031982381)
  ·
    refine ⟨32622026968561842011993393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 86992071916164912031982381 32622026968561842011993393)
    ·
      refine ⟨24466520226421381508995045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32622026968561842011993393 24466520226421381508995045)
      ·
        refine ⟨4587472542454009032936571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24466520226421381508995045 4587472542454009032936571)
        ·
          refine ⟨6881208813681013549404857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4587472542454009032936571 6881208813681013549404857)
          ·
            refine ⟨5160906610260760162053643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6881208813681013549404857 5160906610260760162053643)
            ·
              refine ⟨7741359915391140243080465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5160906610260760162053643 7741359915391140243080465)
              ·
                refine ⟨5806019936543355182310349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7741359915391140243080465 5806019936543355182310349)
                ·
                  refine ⟨2177257476203758193366381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5806019936543355182310349 2177257476203758193366381)
                  ·
                    refine ⟨816471553576409322512393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2177257476203758193366381 816471553576409322512393)
                    ·
                      rfl

theorem cell22_2385109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 2, 3, 3].length) (baseStart_2385109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385109 prefixEnd_2385109 := by exact prefixLift 2385109
  have htrace : WordTrace (prefixWord ++ tailWord_2385109) baseStart_2385109 baseEnd_2385109 := by
    simpa [prefixWord, tailWord_2385109, baseEnd_2385109] using wordTrace_append hprefix tailTrace_2385109
  have hstable : (prefixWord ++ tailWord_2385109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385109).length < 2 ^ (prefixWord ++ tailWord_2385109).sum := by decide
  have hdescent : baseEnd_2385109 < baseStart_2385109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385201 : List Nat := [1, 2, 2, 3, 3, 2, 3, 2, 4]
def baseStart_2385201 : Nat := 118140960795 + 2385201 * 2 ^ 59
def prefixEnd_2385201 : Nat := 4983230072969 + 3 ^ 40 * 2385201 * 2
def baseEnd_2385201 : Nat := 272167682352183916404037

theorem tailTrace_2385201 : CollatzResearch.WordTrace tailWord_2385201 prefixEnd_2385201 272167682352183916404037 := by
  unfold tailWord_2385201
  simp only [CollatzResearch.WordTrace]
  refine ⟨86995427431831611744331457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57996951621221074496220971 86995427431831611744331457)
  ·
    refine ⟨65246570573873708808248593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 86995427431831611744331457 65246570573873708808248593)
    ·
      refine ⟨48934927930405281606186445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65246570573873708808248593 48934927930405281606186445)
      ·
        refine ⟨18350597973901980602319917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48934927930405281606186445 18350597973901980602319917)
        ·
          refine ⟨6881474240213242725869969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18350597973901980602319917 6881474240213242725869969)
          ·
            refine ⟨5161105680159932044402477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6881474240213242725869969 5161105680159932044402477)
            ·
              refine ⟨1935414630059974516650929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5161105680159932044402477 1935414630059974516650929)
              ·
                refine ⟨1451560972544980887488197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1935414630059974516650929 1451560972544980887488197)
                ·
                  refine ⟨272167682352183916404037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1451560972544980887488197 272167682352183916404037)
                  ·
                    rfl

theorem cell22_2385201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 3, 2, 4].length) (baseStart_2385201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385201 prefixEnd_2385201 := by exact prefixLift 2385201
  have htrace : WordTrace (prefixWord ++ tailWord_2385201) baseStart_2385201 baseEnd_2385201 := by
    simpa [prefixWord, tailWord_2385201, baseEnd_2385201] using wordTrace_append hprefix tailTrace_2385201
  have hstable : (prefixWord ++ tailWord_2385201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385201).length < 2 ^ (prefixWord ++ tailWord_2385201).sum := by decide
  have hdescent : baseEnd_2385201 < baseStart_2385201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385212 : List Nat := [2, 2, 2, 2, 1, 4, 2, 7]
def baseStart_2385212 : Nat := 118140960795 + 2385212 * 2 ^ 59
def prefixEnd_2385212 : Nat := 4983230072969 + 3 ^ 40 * 2385212 * 2
def baseEnd_2385212 : Nat := 90722979175705709687453

theorem tailTrace_2385212 : CollatzResearch.WordTrace tailWord_2385212 prefixEnd_2385212 90722979175705709687453 := by
  unfold tailWord_2385212
  simp only [CollatzResearch.WordTrace]
  refine ⟨43497914317395880311490945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57997219089861173748654593 43497914317395880311490945)
  ·
    refine ⟨32623435738046910233618209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43497914317395880311490945 32623435738046910233618209)
    ·
      refine ⟨24467576803535182675213657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32623435738046910233618209 24467576803535182675213657)
      ·
        refine ⟨18350682602651387006410243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24467576803535182675213657 18350682602651387006410243)
        ·
          refine ⟨27526023903977080509615365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18350682602651387006410243 27526023903977080509615365)
          ·
            refine ⟨5161129481995702595552881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27526023903977080509615365 5161129481995702595552881)
            ·
              refine ⟨3870847111496776946664661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5161129481995702595552881 3870847111496776946664661)
              ·
                refine ⟨90722979175705709687453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3870847111496776946664661 90722979175705709687453)
                ·
                  rfl

theorem cell22_2385212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 2, 7].length) (baseStart_2385212 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385212 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385212 prefixEnd_2385212 := by exact prefixLift 2385212
  have htrace : WordTrace (prefixWord ++ tailWord_2385212) baseStart_2385212 baseEnd_2385212 := by
    simpa [prefixWord, tailWord_2385212, baseEnd_2385212] using wordTrace_append hprefix tailTrace_2385212
  have hstable : (prefixWord ++ tailWord_2385212).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385212).length < 2 ^ (prefixWord ++ tailWord_2385212).sum := by decide
  have hdescent : baseEnd_2385212 < baseStart_2385212 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385308 : List Nat := [2, 2, 3, 4, 1, 2, 1, 2, 5]
def baseStart_2385308 : Nat := 118140960795 + 2385308 * 2 ^ 59
def prefixEnd_2385308 : Nat := 4983230072969 + 3 ^ 40 * 2385308 * 2
def baseEnd_2385308 : Nat := 272179891781079712262261

theorem tailTrace_2385308 : CollatzResearch.WordTrace tailWord_2385308 prefixEnd_2385308 272179891781079712262261 := by
  unfold tailWord_2385308
  simp only [CollatzResearch.WordTrace]
  refine ⟨43499665021221984509238289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 57999553361629312678984385 43499665021221984509238289)
  ·
    refine ⟨32624748765916488381928717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43499665021221984509238289 32624748765916488381928717)
    ·
      refine ⟨12234280787218683143223269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32624748765916488381928717 12234280787218683143223269)
      ·
        refine ⟨2293927647603503089354363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12234280787218683143223269 2293927647603503089354363)
        ·
          refine ⟨3440891471405254634031545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2293927647603503089354363 3440891471405254634031545)
          ·
            refine ⟨2580668603553940975523659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3440891471405254634031545 2580668603553940975523659)
            ·
              refine ⟨3871002905330911463285489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580668603553940975523659 3871002905330911463285489)
              ·
                refine ⟨2903252178998183597464117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3871002905330911463285489 2903252178998183597464117)
                ·
                  refine ⟨272179891781079712262261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2903252178998183597464117 272179891781079712262261)
                  ·
                    rfl

theorem cell22_2385308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 1, 2, 5].length) (baseStart_2385308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385308 prefixEnd_2385308 := by exact prefixLift 2385308
  have htrace : WordTrace (prefixWord ++ tailWord_2385308) baseStart_2385308 baseEnd_2385308 := by
    simpa [prefixWord, tailWord_2385308, baseEnd_2385308] using wordTrace_append hprefix tailTrace_2385308
  have hstable : (prefixWord ++ tailWord_2385308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385308).length < 2 ^ (prefixWord ++ tailWord_2385308).sum := by decide
  have hdescent : baseEnd_2385308 < baseStart_2385308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385319 : List Nat := [1, 1, 6, 1, 1, 1, 4, 1, 6]
def baseStart_2385319 : Nat := 118140960795 + 2385319 * 2 ^ 59
def prefixEnd_2385319 : Nat := 4983230072969 + 3 ^ 40 * 2385319 * 2
def baseEnd_2385319 : Nat := 272181146956012924920583

theorem tailTrace_2385319 : CollatzResearch.WordTrace tailWord_2385319 prefixEnd_2385319 272181146956012924920583 := by
  unfold tailWord_2385319
  simp only [CollatzResearch.WordTrace]
  refine ⟨86999731245404117897127011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 57999820830269411931418007 86999731245404117897127011)
  ·
    refine ⟨130499596868106176845690517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 86999731245404117897127011 130499596868106176845690517)
    ·
      refine ⟨6117168603192477039641743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 130499596868106176845690517 6117168603192477039641743)
      ·
        refine ⟨9175752904788715559462615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6117168603192477039641743 9175752904788715559462615)
        ·
          refine ⟨13763629357183073339193923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9175752904788715559462615 13763629357183073339193923)
          ·
            refine ⟨20645444035774610008790885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13763629357183073339193923 20645444035774610008790885)
            ·
              refine ⟨3871020756707739376648291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20645444035774610008790885 3871020756707739376648291)
              ·
                refine ⟨5806531135061609064972437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3871020756707739376648291 5806531135061609064972437)
                ·
                  refine ⟨272181146956012924920583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5806531135061609064972437 272181146956012924920583)
                  ·
                    rfl

theorem cell22_2385319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 1, 6].length) (baseStart_2385319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385319 prefixEnd_2385319 := by exact prefixLift 2385319
  have htrace : WordTrace (prefixWord ++ tailWord_2385319) baseStart_2385319 baseEnd_2385319 := by
    simpa [prefixWord, tailWord_2385319, baseEnd_2385319] using wordTrace_append hprefix tailTrace_2385319
  have hstable : (prefixWord ++ tailWord_2385319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385319).length < 2 ^ (prefixWord ++ tailWord_2385319).sum := by decide
  have hdescent : baseEnd_2385319 < baseStart_2385319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385346 : List Nat := [3, 5, 2, 1, 1, 2, 1, 3, 1, 3]
def baseStart_2385346 : Nat := 118140960795 + 2385346 * 2 ^ 59
def prefixEnd_2385346 : Nat := 4983230072969 + 3 ^ 40 * 2385346 * 2
def baseEnd_2385346 : Nat := 816552683519819704336667

theorem tailTrace_2385346 : CollatzResearch.WordTrace tailWord_2385346 prefixEnd_2385346 816552683519819704336667 := by
  unfold tailWord_2385346
  simp only [CollatzResearch.WordTrace]
  refine ⟨21750179004076575377089973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58000477344204201005573261 21750179004076575377089973)
  ·
    refine ⟨2039079281632178941602185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21750179004076575377089973 2039079281632178941602185)
    ·
      refine ⟨1529309461224134206201639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2039079281632178941602185 1529309461224134206201639)
      ·
        refine ⟨2293964191836201309302459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1529309461224134206201639 2293964191836201309302459)
        ·
          refine ⟨3440946287754301963953689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2293964191836201309302459 3440946287754301963953689)
          ·
            refine ⟨2580709715815726472965267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3440946287754301963953689 2580709715815726472965267)
            ·
              refine ⟨3871064573723589709447901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2580709715815726472965267 3871064573723589709447901)
              ·
                refine ⟨1451649215146346141042963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3871064573723589709447901 1451649215146346141042963)
                ·
                  refine ⟨2177473822719519211564445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1451649215146346141042963 2177473822719519211564445)
                  ·
                    refine ⟨816552683519819704336667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2177473822719519211564445 816552683519819704336667)
                    ·
                      rfl

theorem cell22_2385346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_2385346 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385346 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385346 prefixEnd_2385346 := by exact prefixLift 2385346
  have htrace : WordTrace (prefixWord ++ tailWord_2385346) baseStart_2385346 baseEnd_2385346 := by
    simpa [prefixWord, tailWord_2385346, baseEnd_2385346] using wordTrace_append hprefix tailTrace_2385346
  have hstable : (prefixWord ++ tailWord_2385346).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385346).length < 2 ^ (prefixWord ++ tailWord_2385346).sum := by decide
  have hdescent : baseEnd_2385346 < baseStart_2385346 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385366 : List Nat := [5, 2, 1, 1, 1, 2, 1, 1, 4, 4]
def baseStart_2385366 : Nat := 118140960795 + 2385366 * 2 ^ 59
def prefixEnd_2385366 : Nat := 4983230072969 + 3 ^ 40 * 2385366 * 2
def baseEnd_2385366 : Nat := 816559529928546318836605

theorem tailTrace_2385366 : CollatzResearch.WordTrace tailWord_2385366 prefixEnd_2385366 816559529928546318836605 := by
  unfold tailWord_2385366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5437590342264615307755497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58000963650822563282725301 5437590342264615307755497)
  ·
    refine ⟨4078192756698461480816623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5437590342264615307755497 4078192756698461480816623)
    ·
      refine ⟨6117289135047692221224935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4078192756698461480816623 6117289135047692221224935)
      ·
        refine ⟨9175933702571538331837403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6117289135047692221224935 9175933702571538331837403)
        ·
          refine ⟨13763900553857307497756105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9175933702571538331837403 13763900553857307497756105)
          ·
            refine ⟨10322925415392980623317079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13763900553857307497756105 10322925415392980623317079)
            ·
              refine ⟨15484388123089470934975619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10322925415392980623317079 15484388123089470934975619)
              ·
                refine ⟨23226582184634206402463429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15484388123089470934975619 23226582184634206402463429)
                ·
                  refine ⟨4354984159618913700461893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23226582184634206402463429 4354984159618913700461893)
                  ·
                    refine ⟨816559529928546318836605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4354984159618913700461893 816559529928546318836605)
                    ·
                      rfl

theorem cell22_2385366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_2385366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385366 prefixEnd_2385366 := by exact prefixLift 2385366
  have htrace : WordTrace (prefixWord ++ tailWord_2385366) baseStart_2385366 baseEnd_2385366 := by
    simpa [prefixWord, tailWord_2385366, baseEnd_2385366] using wordTrace_append hprefix tailTrace_2385366
  have hstable : (prefixWord ++ tailWord_2385366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385366).length < 2 ^ (prefixWord ++ tailWord_2385366).sum := by decide
  have hdescent : baseEnd_2385366 < baseStart_2385366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385407 : List Nat := [1, 1, 2, 2, 1, 2, 2, 1, 3, 7]
def baseStart_2385407 : Nat := 118140960795 + 2385407 * 2 ^ 59
def prefixEnd_2385407 : Nat := 4983230072969 + 3 ^ 40 * 2385407 * 2
def baseEnd_2385407 : Nat := 816573565066435878561479

theorem tailTrace_2385407 : CollatzResearch.WordTrace tailWord_2385407 prefixEnd_2385407 816573565066435878561479 := by
  unfold tailWord_2385407
  simp only [CollatzResearch.WordTrace]
  refine ⟨87002940869085308926330475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58001960579390205950886983 87002940869085308926330475)
  ·
    refine ⟨130504411303627963389495713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87002940869085308926330475 130504411303627963389495713)
    ·
      refine ⟨97878308477720972542121785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130504411303627963389495713 97878308477720972542121785)
      ·
        refine ⟨73408731358290729406591339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97878308477720972542121785 73408731358290729406591339)
        ·
          refine ⟨110113097037436094109887009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73408731358290729406591339 110113097037436094109887009)
          ·
            refine ⟨82584822778077070582415257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110113097037436094109887009 82584822778077070582415257)
            ·
              refine ⟨61938617083557802936811443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82584822778077070582415257 61938617083557802936811443)
              ·
                refine ⟨92907925625336704405217165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 61938617083557802936811443 92907925625336704405217165)
                ·
                  refine ⟨34840472109501264151956437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 92907925625336704405217165 34840472109501264151956437)
                  ·
                    refine ⟨816573565066435878561479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34840472109501264151956437 816573565066435878561479)
                    ·
                      rfl

theorem cell22_2385407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 7].length) (baseStart_2385407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385407 prefixEnd_2385407 := by exact prefixLift 2385407
  have htrace : WordTrace (prefixWord ++ tailWord_2385407) baseStart_2385407 baseEnd_2385407 := by
    simpa [prefixWord, tailWord_2385407, baseEnd_2385407] using wordTrace_append hprefix tailTrace_2385407
  have hstable : (prefixWord ++ tailWord_2385407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385407).length < 2 ^ (prefixWord ++ tailWord_2385407).sum := by decide
  have hdescent : baseEnd_2385407 < baseStart_2385407 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385439 : List Nat := [1, 1, 2, 4, 1, 1, 3, 2, 3, 4]
def baseStart_2385439 : Nat := 118140960795 + 2385439 * 2 ^ 59
def prefixEnd_2385439 : Nat := 4983230072969 + 3 ^ 40 * 2385439 * 2
def baseEnd_2385439 : Nat := 816584519320398461761381

theorem tailTrace_2385439 : CollatzResearch.WordTrace tailWord_2385439 prefixEnd_2385439 816584519320398461761381 := by
  unfold tailWord_2385439
  simp only [CollatzResearch.WordTrace]
  refine ⟨87004108004969378391495371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58002738669979585594330247 87004108004969378391495371)
  ·
    refine ⟨130506162007454067587243057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87004108004969378391495371 130506162007454067587243057)
    ·
      refine ⟨97879621505590550690432293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130506162007454067587243057 97879621505590550690432293)
      ·
        refine ⟨18352429032298228254456055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97879621505590550690432293 18352429032298228254456055)
        ·
          refine ⟨27528643548447342381684083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18352429032298228254456055 27528643548447342381684083)
          ·
            refine ⟨41292965322671013572526125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27528643548447342381684083 41292965322671013572526125)
            ·
              refine ⟨15484861996001630089697297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41292965322671013572526125 15484861996001630089697297)
              ·
                refine ⟨11613646497001222567272973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15484861996001630089697297 11613646497001222567272973)
                ·
                  refine ⟨4355117436375458462727365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11613646497001222567272973 4355117436375458462727365)
                  ·
                    refine ⟨816584519320398461761381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4355117436375458462727365 816584519320398461761381)
                    ·
                      rfl

theorem cell22_2385439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_2385439 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385439 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385439 prefixEnd_2385439 := by exact prefixLift 2385439
  have htrace : WordTrace (prefixWord ++ tailWord_2385439) baseStart_2385439 baseEnd_2385439 := by
    simpa [prefixWord, tailWord_2385439, baseEnd_2385439] using wordTrace_append hprefix tailTrace_2385439
  have hstable : (prefixWord ++ tailWord_2385439).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385439).length < 2 ^ (prefixWord ++ tailWord_2385439).sum := by decide
  have hdescent : baseEnd_2385439 < baseStart_2385439 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385471 : List Nat := [1, 1, 2, 2, 3, 3, 1, 5, 4]
def baseStart_2385471 : Nat := 118140960795 + 2385471 * 2 ^ 59
def prefixEnd_2385471 : Nat := 4983230072969 + 3 ^ 40 * 2385471 * 2
def baseEnd_2385471 : Nat := 272198491191453681653761

theorem tailTrace_2385471 : CollatzResearch.WordTrace tailWord_2385471 prefixEnd_2385471 272198491191453681653761 := by
  unfold tailWord_2385471
  simp only [CollatzResearch.WordTrace]
  refine ⟨87005275140853447856660267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58003516760568965237773511 87005275140853447856660267)
  ·
    refine ⟨130507912711280171784990401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87005275140853447856660267 130507912711280171784990401)
    ·
      refine ⟨97880934533460128838742801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130507912711280171784990401 97880934533460128838742801)
      ·
        refine ⟨73410700900095096629057101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97880934533460128838742801 73410700900095096629057101)
        ·
          refine ⟨27529012837535661235896413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 73410700900095096629057101 27529012837535661235896413)
          ·
            refine ⟨10323379814075872963461155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27529012837535661235896413 10323379814075872963461155)
            ·
              refine ⟨15485069721113809445191733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10323379814075872963461155 15485069721113809445191733)
              ·
                refine ⟨1451725286354419635486725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15485069721113809445191733 1451725286354419635486725)
                ·
                  refine ⟨272198491191453681653761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1451725286354419635486725 272198491191453681653761)
                  ·
                    rfl

theorem cell22_2385471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 1, 5, 4].length) (baseStart_2385471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385471 prefixEnd_2385471 := by exact prefixLift 2385471
  have htrace : WordTrace (prefixWord ++ tailWord_2385471) baseStart_2385471 baseEnd_2385471 := by
    simpa [prefixWord, tailWord_2385471, baseEnd_2385471] using wordTrace_append hprefix tailTrace_2385471
  have hstable : (prefixWord ++ tailWord_2385471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385471).length < 2 ^ (prefixWord ++ tailWord_2385471).sum := by decide
  have hdescent : baseEnd_2385471 < baseStart_2385471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385554 : List Nat := [3, 2, 3, 1, 4, 1, 2, 1, 2, 3]
def baseStart_2385554 : Nat := 118140960795 + 2385554 * 2 ^ 59
def prefixEnd_2385554 : Nat := 4983230072969 + 3 ^ 40 * 2385554 * 2
def baseEnd_2385554 : Nat := 816623886170576495136029

theorem tailTrace_2385554 : CollatzResearch.WordTrace tailWord_2385554 prefixEnd_2385554 816623886170576495136029 := by
  unfold tailWord_2385554
  simp only [CollatzResearch.WordTrace]
  refine ⟨21752075599888188257982929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58005534933035168687954477 21752075599888188257982929)
  ·
    refine ⟨16314056699916141193487197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21752075599888188257982929 16314056699916141193487197)
    ·
      refine ⟨6117771262468552947557699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16314056699916141193487197 6117771262468552947557699)
      ·
        refine ⟨9176656893702829421336549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6117771262468552947557699 9176656893702829421336549)
        ·
          refine ⟨1720623167569280516500603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9176656893702829421336549 1720623167569280516500603)
          ·
            refine ⟨2580934751353920774750905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1720623167569280516500603 2580934751353920774750905)
            ·
              refine ⟨1935701063515440581063179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2580934751353920774750905 1935701063515440581063179)
              ·
                refine ⟨2903551595273160871594769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1935701063515440581063179 2903551595273160871594769)
                ·
                  refine ⟨2177663696454870653696077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2903551595273160871594769 2177663696454870653696077)
                  ·
                    refine ⟨816623886170576495136029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2177663696454870653696077 816623886170576495136029)
                    ·
                      rfl

theorem cell22_2385554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_2385554 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385554 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385554 prefixEnd_2385554 := by exact prefixLift 2385554
  have htrace : WordTrace (prefixWord ++ tailWord_2385554) baseStart_2385554 baseEnd_2385554 := by
    simpa [prefixWord, tailWord_2385554, baseEnd_2385554] using wordTrace_append hprefix tailTrace_2385554
  have hstable : (prefixWord ++ tailWord_2385554).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385554).length < 2 ^ (prefixWord ++ tailWord_2385554).sum := by decide
  have hdescent : baseEnd_2385554 < baseStart_2385554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385619 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 2, 10]
def baseStart_2385619 : Nat := 118140960795 + 2385619 * 2 ^ 59
def prefixEnd_2385619 : Nat := 4983230072969 + 3 ^ 40 * 2385619 * 2
def baseEnd_2385619 : Nat := 816646136998937992260829

theorem tailTrace_2385619 : CollatzResearch.WordTrace tailWord_2385619 prefixEnd_2385619 816646136998937992260829 := by
  unfold tailWord_2385619
  simp only [CollatzResearch.WordTrace]
  refine ⟨87010673144317269133047911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58007115429544846088698607 87010673144317269133047911)
  ·
    refine ⟨130516009716475903699571867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87010673144317269133047911 130516009716475903699571867)
    ·
      refine ⟨195774014574713855549357801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130516009716475903699571867 195774014574713855549357801)
      ·
        refine ⟨146830510931035391662018351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195774014574713855549357801 146830510931035391662018351)
        ·
          refine ⟨220245766396553087493027527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146830510931035391662018351 220245766396553087493027527)
          ·
            refine ⟨330368649594829631239541291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 220245766396553087493027527 330368649594829631239541291)
            ·
              refine ⟨495552974392244446859311937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 330368649594829631239541291 495552974392244446859311937)
              ·
                refine ⟨371664730794183335144483953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 495552974392244446859311937 371664730794183335144483953)
                ·
                  refine ⟨278748548095637501358362965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 371664730794183335144483953 278748548095637501358362965)
                  ·
                    refine ⟨816646136998937992260829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 278748548095637501358362965 816646136998937992260829)
                    ·
                      rfl

theorem cell22_2385619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 10].length) (baseStart_2385619 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385619 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385619 prefixEnd_2385619 := by exact prefixLift 2385619
  have htrace : WordTrace (prefixWord ++ tailWord_2385619) baseStart_2385619 baseEnd_2385619 := by
    simpa [prefixWord, tailWord_2385619, baseEnd_2385619] using wordTrace_append hprefix tailTrace_2385619
  have hstable : (prefixWord ++ tailWord_2385619).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385619).length < 2 ^ (prefixWord ++ tailWord_2385619).sum := by decide
  have hdescent : baseEnd_2385619 < baseStart_2385619 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385636 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 1, 6]
def baseStart_2385636 : Nat := 118140960795 + 2385636 * 2 ^ 59
def prefixEnd_2385636 : Nat := 4983230072969 + 3 ^ 40 * 2385636 * 2
def baseEnd_2385636 : Nat := 816651956446355614585777

theorem tailTrace_2385636 : CollatzResearch.WordTrace tailWord_2385636 prefixEnd_2385636 816651956446355614585777 := by
  unfold tailWord_2385636
  simp only [CollatzResearch.WordTrace]
  refine ⟨43505646592627840518208381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58007528790170454024277841 43505646592627840518208381)
  ·
    refine ⟨16314617472235440194328143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43505646592627840518208381 16314617472235440194328143)
    ·
      refine ⟨24471926208353160291492215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16314617472235440194328143 24471926208353160291492215)
      ·
        refine ⟨36707889312529740437238323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24471926208353160291492215 36707889312529740437238323)
        ·
          refine ⟨55061833968794610655857485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36707889312529740437238323 55061833968794610655857485)
          ·
            refine ⟨20648187738297978995946557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55061833968794610655857485 20648187738297978995946557)
            ·
              refine ⟨7743070401861742123479959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 20648187738297978995946557 7743070401861742123479959)
              ·
                refine ⟨11614605602792613185219939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7743070401861742123479959 11614605602792613185219939)
                ·
                  refine ⟨17421908404188919777829909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11614605602792613185219939 17421908404188919777829909)
                  ·
                    refine ⟨816651956446355614585777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17421908404188919777829909 816651956446355614585777)
                    ·
                      rfl

theorem cell22_2385636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 1, 6].length) (baseStart_2385636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385636 prefixEnd_2385636 := by exact prefixLift 2385636
  have htrace : WordTrace (prefixWord ++ tailWord_2385636) baseStart_2385636 baseEnd_2385636 := by
    simpa [prefixWord, tailWord_2385636, baseEnd_2385636] using wordTrace_append hprefix tailTrace_2385636
  have hstable : (prefixWord ++ tailWord_2385636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385636).length < 2 ^ (prefixWord ++ tailWord_2385636).sum := by decide
  have hdescent : baseEnd_2385636 < baseStart_2385636 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385640 : List Nat := [2, 1, 4, 1, 3, 2, 2, 3, 4]
def baseStart_2385640 : Nat := 118140960795 + 2385640 * 2 ^ 59
def prefixEnd_2385640 : Nat := 4983230072969 + 3 ^ 40 * 2385640 * 2
def baseEnd_2385640 : Nat := 272217775242700312495255

theorem tailTrace_2385640 : CollatzResearch.WordTrace tailWord_2385640 prefixEnd_2385640 272217775242700312495255 := by
  unfold tailWord_2385640
  simp only [CollatzResearch.WordTrace]
  refine ⟨43505719538620594859781187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58007626051494126479708249 43505719538620594859781187)
  ·
    refine ⟨65258579307930892289671781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43505719538620594859781187 65258579307930892289671781)
    ·
      refine ⟨12235983620237042304313459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65258579307930892289671781 12235983620237042304313459)
      ·
        refine ⟨18353975430355563456470189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12235983620237042304313459 18353975430355563456470189)
        ·
          refine ⟨6882740786383336296176321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18353975430355563456470189 6882740786383336296176321)
          ·
            refine ⟨5162055589787502222132241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6882740786383336296176321 5162055589787502222132241)
            ·
              refine ⟨3871541692340626666599181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5162055589787502222132241 3871541692340626666599181)
              ·
                refine ⟨1451828134627734999974693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3871541692340626666599181 1451828134627734999974693)
                ·
                  refine ⟨272217775242700312495255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1451828134627734999974693 272217775242700312495255)
                  ·
                    rfl

theorem cell22_2385640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 3, 4].length) (baseStart_2385640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385640 prefixEnd_2385640 := by exact prefixLift 2385640
  have htrace : WordTrace (prefixWord ++ tailWord_2385640) baseStart_2385640 baseEnd_2385640 := by
    simpa [prefixWord, tailWord_2385640, baseEnd_2385640] using wordTrace_append hprefix tailTrace_2385640
  have hstable : (prefixWord ++ tailWord_2385640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385640).length < 2 ^ (prefixWord ++ tailWord_2385640).sum := by decide
  have hdescent : baseEnd_2385640 < baseStart_2385640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385696 : List Nat := [2, 1, 1, 5, 1, 1, 1, 1, 9]
def baseStart_2385696 : Nat := 118140960795 + 2385696 * 2 ^ 59
def prefixEnd_2385696 : Nat := 4983230072969 + 3 ^ 40 * 2385696 * 2
def baseEnd_2385696 : Nat := 272224165224178486028531

theorem tailTrace_2385696 : CollatzResearch.WordTrace tailWord_2385696 prefixEnd_2385696 272224165224178486028531 := by
  unfold tailWord_2385696
  simp only [CollatzResearch.WordTrace]
  refine ⟨43506740782519155641800471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58008987710025540855733961 43506740782519155641800471)
  ·
    refine ⟨65260111173778733462700707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43506740782519155641800471 65260111173778733462700707)
    ·
      refine ⟨97890166760668100194051061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65260111173778733462700707 97890166760668100194051061)
      ·
        refine ⟨9177203133812634393192287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97890166760668100194051061 9177203133812634393192287)
        ·
          refine ⟨13765804700718951589788431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9177203133812634393192287 13765804700718951589788431)
          ·
            refine ⟨20648707051078427384682647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13765804700718951589788431 20648707051078427384682647)
            ·
              refine ⟨30973060576617641077023971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20648707051078427384682647 30973060576617641077023971)
              ·
                refine ⟨46459590864926461615535957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30973060576617641077023971 46459590864926461615535957)
                ·
                  refine ⟨272224165224178486028531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46459590864926461615535957 272224165224178486028531)
                  ·
                    rfl

theorem cell22_2385696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 1, 9].length) (baseStart_2385696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385696 prefixEnd_2385696 := by exact prefixLift 2385696
  have htrace : WordTrace (prefixWord ++ tailWord_2385696) baseStart_2385696 baseEnd_2385696 := by
    simpa [prefixWord, tailWord_2385696, baseEnd_2385696] using wordTrace_append hprefix tailTrace_2385696
  have hstable : (prefixWord ++ tailWord_2385696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385696).length < 2 ^ (prefixWord ++ tailWord_2385696).sum := by decide
  have hdescent : baseEnd_2385696 < baseStart_2385696 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385717 : List Nat := [1, 3, 3, 1, 4, 2, 1, 1, 3, 3]
def baseStart_2385717 : Nat := 118140960795 + 2385717 * 2 ^ 59
def prefixEnd_2385717 : Nat := 4983230072969 + 3 ^ 40 * 2385717 * 2
def baseEnd_2385717 : Nat := 816679684401698403310529

theorem tailTrace_2385717 : CollatzResearch.WordTrace tailWord_2385717 prefixEnd_2385717 816679684401698403310529 := by
  unfold tailWord_2385717
  simp only [CollatzResearch.WordTrace]
  refine ⟨87014247497962231870115405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58009498331974821246743603 87014247497962231870115405)
  ·
    refine ⟨32630342811735836951293277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87014247497962231870115405 32630342811735836951293277)
    ·
      refine ⟨12236378554400938856734979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32630342811735836951293277 12236378554400938856734979)
      ·
        refine ⟨18354567831601408285102469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12236378554400938856734979 18354567831601408285102469)
        ·
          refine ⟨3441481468425264053456713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18354567831601408285102469 3441481468425264053456713)
          ·
            refine ⟨2581111101318948040092535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3441481468425264053456713 2581111101318948040092535)
            ·
              refine ⟨3871666651978422060138803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2581111101318948040092535 3871666651978422060138803)
              ·
                refine ⟨5807499977967633090208205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3871666651978422060138803 5807499977967633090208205)
                ·
                  refine ⟨2177812491737862408828077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5807499977967633090208205 2177812491737862408828077)
                  ·
                    refine ⟨816679684401698403310529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2177812491737862408828077 816679684401698403310529)
                    ·
                      rfl

theorem cell22_2385717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_2385717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385717 prefixEnd_2385717 := by exact prefixLift 2385717
  have htrace : WordTrace (prefixWord ++ tailWord_2385717) baseStart_2385717 baseEnd_2385717 := by
    simpa [prefixWord, tailWord_2385717, baseEnd_2385717] using wordTrace_append hprefix tailTrace_2385717
  have hstable : (prefixWord ++ tailWord_2385717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385717).length < 2 ^ (prefixWord ++ tailWord_2385717).sum := by decide
  have hdescent : baseEnd_2385717 < baseStart_2385717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385771 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 3, 6]
def baseStart_2385771 : Nat := 118140960795 + 2385771 * 2 ^ 59
def prefixEnd_2385771 : Nat := 4983230072969 + 3 ^ 40 * 2385771 * 2
def baseEnd_2385771 : Nat := 816698169705260262460363

theorem tailTrace_2385771 : CollatzResearch.WordTrace tailWord_2385771 prefixEnd_2385771 816698169705260262460363 := by
  unfold tailWord_2385771
  simp only [CollatzResearch.WordTrace]
  refine ⟨87016217039766599092581167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58010811359844399395054111 87016217039766599092581167)
  ·
    refine ⟨130524325559649898638871751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87016217039766599092581167 130524325559649898638871751)
    ·
      refine ⟨195786488339474847958307627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130524325559649898638871751 195786488339474847958307627)
      ·
        refine ⟨293679732509212271937461441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195786488339474847958307627 293679732509212271937461441)
        ·
          refine ⟨220259799381909203953096081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 293679732509212271937461441 220259799381909203953096081)
          ·
            refine ⟨165194849536431902964822061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220259799381909203953096081 165194849536431902964822061)
            ·
              refine ⟨61948068576161963611808273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 165194849536431902964822061 61948068576161963611808273)
              ·
                refine ⟨46461051432121472708856205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61948068576161963611808273 46461051432121472708856205)
                ·
                  refine ⟨17422894287045552265821077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 46461051432121472708856205 17422894287045552265821077)
                  ·
                    refine ⟨816698169705260262460363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17422894287045552265821077 816698169705260262460363)
                    ·
                      rfl

theorem cell22_2385771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 6].length) (baseStart_2385771 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385771 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385771 prefixEnd_2385771 := by exact prefixLift 2385771
  have htrace : WordTrace (prefixWord ++ tailWord_2385771) baseStart_2385771 baseEnd_2385771 := by
    simpa [prefixWord, tailWord_2385771, baseEnd_2385771] using wordTrace_append hprefix tailTrace_2385771
  have hstable : (prefixWord ++ tailWord_2385771).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385771).length < 2 ^ (prefixWord ++ tailWord_2385771).sum := by decide
  have hdescent : baseEnd_2385771 < baseStart_2385771 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385923 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 1, 6]
def baseStart_2385923 : Nat := 118140960795 + 2385923 * 2 ^ 59
def prefixEnd_2385923 : Nat := 4983230072969 + 3 ^ 40 * 2385923 * 2
def baseEnd_2385923 : Nat := 816750202411582532659897

theorem tailTrace_2385923 : CollatzResearch.WordTrace tailWord_2385923 prefixEnd_2385923 816750202411582532659897 := by
  unfold tailWord_2385923
  simp only [CollatzResearch.WordTrace]
  refine ⟨87021760935215929052114423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58014507290143952701409615 87021760935215929052114423)
  ·
    refine ⟨130532641402823893578171635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87021760935215929052114423 130532641402823893578171635)
    ·
      refine ⟨195798962104235840367257453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130532641402823893578171635 195798962104235840367257453)
      ·
        refine ⟨73424610789088440137721545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195798962104235840367257453 73424610789088440137721545)
        ·
          refine ⟨55068458091816330103291159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73424610789088440137721545 55068458091816330103291159)
          ·
            refine ⟨82602687137724495154936739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55068458091816330103291159 82602687137724495154936739)
            ·
              refine ⟨123904030706586742732405109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82602687137724495154936739 123904030706586742732405109)
              ·
                refine ⟨11616002878742507131162979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 123904030706586742732405109 11616002878742507131162979)
                ·
                  refine ⟨17424004318113760696744469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11616002878742507131162979 17424004318113760696744469)
                  ·
                    refine ⟨816750202411582532659897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17424004318113760696744469 816750202411582532659897)
                    ·
                      rfl

theorem cell22_2385923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 1, 6].length) (baseStart_2385923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385923 prefixEnd_2385923 := by exact prefixLift 2385923
  have htrace : WordTrace (prefixWord ++ tailWord_2385923) baseStart_2385923 baseEnd_2385923 := by
    simpa [prefixWord, tailWord_2385923, baseEnd_2385923] using wordTrace_append hprefix tailTrace_2385923
  have hstable : (prefixWord ++ tailWord_2385923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385923).length < 2 ^ (prefixWord ++ tailWord_2385923).sum := by decide
  have hdescent : baseEnd_2385923 < baseStart_2385923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385925 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 1, 5]
def baseStart_2385925 : Nat := 118140960795 + 2385925 * 2 ^ 59
def prefixEnd_2385925 : Nat := 4983230072969 + 3 ^ 40 * 2385925 * 2
def baseEnd_2385925 : Nat := 816750887052455194109891

theorem tailTrace_2385925 : CollatzResearch.WordTrace tailWord_2385925 prefixEnd_2385925 816750887052455194109891 := by
  unfold tailWord_2385925
  simp only [CollatzResearch.WordTrace]
  refine ⟨87021833881208683393687229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58014555920805788929124819 87021833881208683393687229)
  ·
    refine ⟨32633187705453256272632711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87021833881208683393687229 32633187705453256272632711)
    ·
      refine ⟨48949781558179884408949067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32633187705453256272632711 48949781558179884408949067)
      ·
        refine ⟨73424672337269826613423601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48949781558179884408949067 73424672337269826613423601)
        ·
          refine ⟨55068504252952369960067701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73424672337269826613423601 55068504252952369960067701)
          ·
            refine ⟨5162672273714284683756347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 55068504252952369960067701 5162672273714284683756347)
            ·
              refine ⟨7744008410571427025634521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5162672273714284683756347 7744008410571427025634521)
              ·
                refine ⟨5808006307928570269225891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7744008410571427025634521 5808006307928570269225891)
                ·
                  refine ⟨8712009461892855403838837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5808006307928570269225891 8712009461892855403838837)
                  ·
                    refine ⟨816750887052455194109891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8712009461892855403838837 816750887052455194109891)
                    ·
                      rfl

theorem cell22_2385925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 5].length) (baseStart_2385925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385925 prefixEnd_2385925 := by exact prefixLift 2385925
  have htrace : WordTrace (prefixWord ++ tailWord_2385925) baseStart_2385925 baseEnd_2385925 := by
    simpa [prefixWord, tailWord_2385925, baseEnd_2385925] using wordTrace_append hprefix tailTrace_2385925
  have hstable : (prefixWord ++ tailWord_2385925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385925).length < 2 ^ (prefixWord ++ tailWord_2385925).sum := by decide
  have hdescent : baseEnd_2385925 < baseStart_2385925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2385959 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2385959 : Nat := 118140960795 + 2385959 * 2 ^ 59
def prefixEnd_2385959 : Nat := 4983230072969 + 3 ^ 40 * 2385959 * 2
def baseEnd_2385959 : Nat := 816762525947290438759787

theorem tailTrace_2385959 : CollatzResearch.WordTrace tailWord_2385959 prefixEnd_2385959 816762525947290438759787 := by
  unfold tailWord_2385959
  simp only [CollatzResearch.WordTrace]
  refine ⟨87023073963085507200424931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58015382642057004800283287 87023073963085507200424931)
  ·
    refine ⟨130534610944628260800637397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87023073963085507200424931 130534610944628260800637397)
    ·
      refine ⟨3059404944014724862514939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 130534610944628260800637397 3059404944014724862514939)
      ·
        refine ⟨4589107416022087293772409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3059404944014724862514939 4589107416022087293772409)
        ·
          refine ⟨3441830562016565470329307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4589107416022087293772409 3441830562016565470329307)
          ·
            refine ⟨5162745843024848205493961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3441830562016565470329307 5162745843024848205493961)
            ·
              refine ⟨3872059382268636154120471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5162745843024848205493961 3872059382268636154120471)
              ·
                refine ⟨5808089073402954231180707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3872059382268636154120471 5808089073402954231180707)
                ·
                  refine ⟨8712133610104431346771061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5808089073402954231180707 8712133610104431346771061)
                  ·
                    refine ⟨816762525947290438759787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8712133610104431346771061 816762525947290438759787)
                    ·
                      rfl

theorem cell22_2385959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2385959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2385959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2385959 prefixEnd_2385959 := by exact prefixLift 2385959
  have htrace : WordTrace (prefixWord ++ tailWord_2385959) baseStart_2385959 baseEnd_2385959 := by
    simpa [prefixWord, tailWord_2385959, baseEnd_2385959] using wordTrace_append hprefix tailTrace_2385959
  have hstable : (prefixWord ++ tailWord_2385959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2385959).length < 2 ^ (prefixWord ++ tailWord_2385959).sum := by decide
  have hdescent : baseEnd_2385959 < baseStart_2385959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2385959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386038 : List Nat := [5, 1, 1, 2, 1, 4, 1, 3, 1, 3]
def baseStart_2386038 : Nat := 118140960795 + 2386038 * 2 ^ 59
def prefixEnd_2386038 : Nat := 4983230072969 + 3 ^ 40 * 2386038 * 2
def baseEnd_2386038 : Nat := 816789569261760566034545

theorem tailTrace_2386038 : CollatzResearch.WordTrace tailWord_2386038 prefixEnd_2386038 816789569261760566034545 := by
  unfold tailWord_2386038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5439122208112456480784423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58017303553199535795033845 5439122208112456480784423)
  ·
    refine ⟨8158683312168684721176635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5439122208112456480784423 8158683312168684721176635)
    ·
      refine ⟨12238024968253027081764953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8158683312168684721176635 12238024968253027081764953)
      ·
        refine ⟨9178518726189770311323715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12238024968253027081764953 9178518726189770311323715)
        ·
          refine ⟨13767778089284655466985573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9178518726189770311323715 13767778089284655466985573)
          ·
            refine ⟨2581458391740872900059795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13767778089284655466985573 2581458391740872900059795)
            ·
              refine ⟨3872187587611309350089693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2581458391740872900059795 3872187587611309350089693)
              ·
                refine ⟨1452070345354241006283635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3872187587611309350089693 1452070345354241006283635)
                ·
                  refine ⟨2178105518031361509425453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452070345354241006283635 2178105518031361509425453)
                  ·
                    refine ⟨816789569261760566034545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178105518031361509425453 816789569261760566034545)
                    ·
                      rfl

theorem cell22_2386038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_2386038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386038 prefixEnd_2386038 := by exact prefixLift 2386038
  have htrace : WordTrace (prefixWord ++ tailWord_2386038) baseStart_2386038 baseEnd_2386038 := by
    simpa [prefixWord, tailWord_2386038, baseEnd_2386038] using wordTrace_append hprefix tailTrace_2386038
  have hstable : (prefixWord ++ tailWord_2386038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386038).length < 2 ^ (prefixWord ++ tailWord_2386038).sum := by decide
  have hdescent : baseEnd_2386038 < baseStart_2386038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386068 : List Nat := [2, 4, 2, 3, 1, 2, 2, 1, 5]
def baseStart_2386068 : Nat := 118140960795 + 2386068 * 2 ^ 59
def prefixEnd_2386068 : Nat := 4983230072969 + 3 ^ 40 * 2386068 * 2
def baseEnd_2386068 : Nat := 272266612958283495928151

theorem tailTrace_2386068 : CollatzResearch.WordTrace tailWord_2386068 prefixEnd_2386068 272266612958283495928151 := by
  unfold tailWord_2386068
  simp only [CollatzResearch.WordTrace]
  refine ⟨43513524759845309408071429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58018033013127079210761905 43513524759845309408071429)
  ·
    refine ⟨8158785892470995514013393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43513524759845309408071429 8158785892470995514013393)
    ·
      refine ⟨6119089419353246635510045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8158785892470995514013393 6119089419353246635510045)
      ·
        refine ⟨2294658532257467488316267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6119089419353246635510045 2294658532257467488316267)
        ·
          refine ⟨3441987798386201232474401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2294658532257467488316267 3441987798386201232474401)
          ·
            refine ⟨2581490848789650924355801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3441987798386201232474401 2581490848789650924355801)
            ·
              refine ⟨1936118136592238193266851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2581490848789650924355801 1936118136592238193266851)
              ·
                refine ⟨2904177204888357289900277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1936118136592238193266851 2904177204888357289900277)
                ·
                  refine ⟨272266612958283495928151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2904177204888357289900277 272266612958283495928151)
                  ·
                    rfl

theorem cell22_2386068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_2386068 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386068 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386068 prefixEnd_2386068 := by exact prefixLift 2386068
  have htrace : WordTrace (prefixWord ++ tailWord_2386068) baseStart_2386068 baseEnd_2386068 := by
    simpa [prefixWord, tailWord_2386068, baseEnd_2386068] using wordTrace_append hprefix tailTrace_2386068
  have hstable : (prefixWord ++ tailWord_2386068).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386068).length < 2 ^ (prefixWord ++ tailWord_2386068).sum := by decide
  have hdescent : baseEnd_2386068 < baseStart_2386068 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386075 : List Nat := [1, 1, 1, 1, 1, 1, 2, 6, 4, 4]
def baseStart_2386075 : Nat := 118140960795 + 2386075 * 2 ^ 59
def prefixEnd_2386075 : Nat := 4983230072969 + 3 ^ 40 * 2386075 * 2
def baseEnd_2386075 : Nat := 816802235117904802859431

theorem tailTrace_2386075 : CollatzResearch.WordTrace tailWord_2386075 prefixEnd_2386075 816802235117904802859431 := by
  unfold tailWord_2386075
  simp only [CollatzResearch.WordTrace]
  refine ⟨87027304830665259011647679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58018203220443506007765119 87027304830665259011647679)
  ·
    refine ⟨130540957245997888517471519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87027304830665259011647679 130540957245997888517471519)
    ·
      refine ⟨195811435868996832776207279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130540957245997888517471519 195811435868996832776207279)
      ·
        refine ⟨293717153803495249164310919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195811435868996832776207279 293717153803495249164310919)
        ·
          refine ⟨440575730705242873746466379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 293717153803495249164310919 440575730705242873746466379)
          ·
            refine ⟨660863596057864310619699569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 440575730705242873746466379 660863596057864310619699569)
            ·
              refine ⟨495647697043398232964774677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 660863596057864310619699569 495647697043398232964774677)
              ·
                refine ⟨23233485798909292170223813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 495647697043398232964774677 23233485798909292170223813)
                ·
                  refine ⟨4356278587295492281916965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23233485798909292170223813 4356278587295492281916965)
                  ·
                    refine ⟨816802235117904802859431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4356278587295492281916965 816802235117904802859431)
                    ·
                      rfl

theorem cell22_2386075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 4].length) (baseStart_2386075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386075 prefixEnd_2386075 := by exact prefixLift 2386075
  have htrace : WordTrace (prefixWord ++ tailWord_2386075) baseStart_2386075 baseEnd_2386075 := by
    simpa [prefixWord, tailWord_2386075, baseEnd_2386075] using wordTrace_append hprefix tailTrace_2386075
  have hstable : (prefixWord ++ tailWord_2386075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386075).length < 2 ^ (prefixWord ++ tailWord_2386075).sum := by decide
  have hdescent : baseEnd_2386075 < baseStart_2386075 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386135 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 9]
def baseStart_2386135 : Nat := 118140960795 + 2386135 * 2 ^ 59
def prefixEnd_2386135 : Nat := 4983230072969 + 3 ^ 40 * 2386135 * 2
def baseEnd_2386135 : Nat := 272274258114694882119749

theorem tailTrace_2386135 : CollatzResearch.WordTrace tailWord_2386135 prefixEnd_2386135 272274258114694882119749 := by
  unfold tailWord_2386135
  simp only [CollatzResearch.WordTrace]
  refine ⟨87029493210447889258831859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58019662140298592839221239 87029493210447889258831859)
  ·
    refine ⟨130544239815671833888247789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87029493210447889258831859 130544239815671833888247789)
    ·
      refine ⟨48954089930876937708092921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130544239815671833888247789 48954089930876937708092921)
      ·
        refine ⟨36715567448157703281069691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48954089930876937708092921 36715567448157703281069691)
        ·
          refine ⟨55073351172236554921604537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36715567448157703281069691 55073351172236554921604537)
          ·
            refine ⟨41305013379177416191203403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55073351172236554921604537 41305013379177416191203403)
            ·
              refine ⟨61957520068766124286805105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41305013379177416191203403 61957520068766124286805105)
              ·
                refine ⟨46468140051574593215103829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61957520068766124286805105 46468140051574593215103829)
                ·
                  refine ⟨272274258114694882119749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 46468140051574593215103829 272274258114694882119749)
                  ·
                    rfl

theorem cell22_2386135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 9].length) (baseStart_2386135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386135 prefixEnd_2386135 := by exact prefixLift 2386135
  have htrace : WordTrace (prefixWord ++ tailWord_2386135) baseStart_2386135 baseEnd_2386135 := by
    simpa [prefixWord, tailWord_2386135, baseEnd_2386135] using wordTrace_append hprefix tailTrace_2386135
  have hstable : (prefixWord ++ tailWord_2386135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386135).length < 2 ^ (prefixWord ++ tailWord_2386135).sum := by decide
  have hdescent : baseEnd_2386135 < baseStart_2386135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386156 : List Nat := [2, 2, 1, 1, 2, 3, 4, 3, 1, 3]
def baseStart_2386156 : Nat := 118140960795 + 2386156 * 2 ^ 59
def prefixEnd_2386156 : Nat := 4983230072969 + 3 ^ 40 * 2386156 * 2
def baseEnd_2386156 : Nat := 816829963073247591584183

theorem tailTrace_2386156 : CollatzResearch.WordTrace tailWord_2386156 prefixEnd_2386156 816829963073247591584183 := by
  unfold tailWord_2386156
  simp only [CollatzResearch.WordTrace]
  refine ⟨43515129571685904922673161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58020172762247873230230881 43515129571685904922673161)
  ·
    refine ⟨32636347178764428692004871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43515129571685904922673161 32636347178764428692004871)
    ·
      refine ⟨48954520768146643038007307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32636347178764428692004871 48954520768146643038007307)
      ·
        refine ⟨73431781152219964557010961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48954520768146643038007307 73431781152219964557010961)
        ·
          refine ⟨55073835864164973417758221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73431781152219964557010961 55073835864164973417758221)
          ·
            refine ⟨20652688449061865031659333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55073835864164973417758221 20652688449061865031659333)
            ·
              refine ⟨3872379084199099693436125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20652688449061865031659333 3872379084199099693436125)
              ·
                refine ⟨1452142156574662385038547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3872379084199099693436125 1452142156574662385038547)
                ·
                  refine ⟨2178213234861993577557821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452142156574662385038547 2178213234861993577557821)
                  ·
                    refine ⟨816829963073247591584183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178213234861993577557821 816829963073247591584183)
                    ·
                      rfl

theorem cell22_2386156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_2386156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386156 prefixEnd_2386156 := by exact prefixLift 2386156
  have htrace : WordTrace (prefixWord ++ tailWord_2386156) baseStart_2386156 baseEnd_2386156 := by
    simpa [prefixWord, tailWord_2386156, baseEnd_2386156] using wordTrace_append hprefix tailTrace_2386156
  have hstable : (prefixWord ++ tailWord_2386156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386156).length < 2 ^ (prefixWord ++ tailWord_2386156).sum := by decide
  have hdescent : baseEnd_2386156 < baseStart_2386156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386197 : List Nat := [1, 3, 2, 1, 2, 1, 4, 2, 6]
def baseStart_2386197 : Nat := 118140960795 + 2386197 * 2 ^ 59
def prefixEnd_2386197 : Nat := 4983230072969 + 3 ^ 40 * 2386197 * 2
def baseEnd_2386197 : Nat := 272281332737045717103019

theorem tailTrace_2386197 : CollatzResearch.WordTrace tailWord_2386197 prefixEnd_2386197 272281332737045717103019 := by
  unfold tailWord_2386197
  simp only [CollatzResearch.WordTrace]
  refine ⟨87031754536223273847588845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58021169690815515898392563 87031754536223273847588845)
  ·
    refine ⟨32636907951083727692845817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87031754536223273847588845 32636907951083727692845817)
    ·
      refine ⟨24477680963312795769634363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32636907951083727692845817 24477680963312795769634363)
      ·
        refine ⟨36716521444969193654451545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24477680963312795769634363 36716521444969193654451545)
        ·
          refine ⟨27537391083726895240838659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36716521444969193654451545 27537391083726895240838659)
          ·
            refine ⟨41306086625590342861257989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27537391083726895240838659 41306086625590342861257989)
            ·
              refine ⟨7744891242298189286485873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41306086625590342861257989 7744891242298189286485873)
              ·
                refine ⟨5808668431723641964864405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7744891242298189286485873 5808668431723641964864405)
                ·
                  refine ⟨272281332737045717103019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5808668431723641964864405 272281332737045717103019)
                  ·
                    rfl

theorem cell22_2386197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 2, 6].length) (baseStart_2386197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386197 prefixEnd_2386197 := by exact prefixLift 2386197
  have htrace : WordTrace (prefixWord ++ tailWord_2386197) baseStart_2386197 baseEnd_2386197 := by
    simpa [prefixWord, tailWord_2386197, baseEnd_2386197] using wordTrace_append hprefix tailTrace_2386197
  have hstable : (prefixWord ++ tailWord_2386197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386197).length < 2 ^ (prefixWord ++ tailWord_2386197).sum := by decide
  have hdescent : baseEnd_2386197 < baseStart_2386197 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386199 : List Nat := [1, 1, 3, 4, 1, 2, 1, 4, 1, 4]
def baseStart_2386199 : Nat := 118140960795 + 2386199 * 2 ^ 59
def prefixEnd_2386199 : Nat := 4983230072969 + 3 ^ 40 * 2386199 * 2
def baseEnd_2386199 : Nat := 816844682852009812759051

theorem tailTrace_2386199 : CollatzResearch.WordTrace tailWord_2386199 prefixEnd_2386199 816844682852009812759051 := by
  unfold tailWord_2386199
  simp only [CollatzResearch.WordTrace]
  refine ⟨87031827482216028189161651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58021218321477352126107767 87031827482216028189161651)
  ·
    refine ⟨130547741223324042283742477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87031827482216028189161651 130547741223324042283742477)
    ·
      refine ⟨48955402958746515856403429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130547741223324042283742477 48955402958746515856403429)
      ·
        refine ⟨9179138054764971723075643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48955402958746515856403429 9179138054764971723075643)
        ·
          refine ⟨13768707082147457584613465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9179138054764971723075643 13768707082147457584613465)
          ·
            refine ⟨10326530311610593188460099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13768707082147457584613465 10326530311610593188460099)
            ·
              refine ⟨15489795467415889782690149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10326530311610593188460099 15489795467415889782690149)
              ·
                refine ⟨2904336650140479334254403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15489795467415889782690149 2904336650140479334254403)
                ·
                  refine ⟨4356504975210719001381605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904336650140479334254403 4356504975210719001381605)
                  ·
                    refine ⟨816844682852009812759051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4356504975210719001381605 816844682852009812759051)
                    ·
                      rfl

theorem cell22_2386199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 4].length) (baseStart_2386199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386199 prefixEnd_2386199 := by exact prefixLift 2386199
  have htrace : WordTrace (prefixWord ++ tailWord_2386199) baseStart_2386199 baseEnd_2386199 := by
    simpa [prefixWord, tailWord_2386199, baseEnd_2386199] using wordTrace_append hprefix tailTrace_2386199
  have hstable : (prefixWord ++ tailWord_2386199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386199).length < 2 ^ (prefixWord ++ tailWord_2386199).sum := by decide
  have hdescent : baseEnd_2386199 < baseStart_2386199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386229 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 4, 3]
def baseStart_2386229 : Nat := 118140960795 + 2386229 * 2 ^ 59
def prefixEnd_2386229 : Nat := 4983230072969 + 3 ^ 40 * 2386229 * 2
def baseEnd_2386229 : Nat := 816854952465099734508959

theorem tailTrace_2386229 : CollatzResearch.WordTrace tailWord_2386229 prefixEnd_2386229 816854952465099734508959 := by
  unfold tailWord_2386229
  simp only [CollatzResearch.WordTrace]
  refine ⟨87032921672107343312753741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58021947781404895541835827 87032921672107343312753741)
  ·
    refine ⟨32637345627040253742282653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87032921672107343312753741 32637345627040253742282653)
    ·
      refine ⟨12239004610140095153355995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32637345627040253742282653 12239004610140095153355995)
      ·
        refine ⟨18358506915210142730033993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12239004610140095153355995 18358506915210142730033993)
        ·
          refine ⟨13768880186407607047525495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18358506915210142730033993 13768880186407607047525495)
          ·
            refine ⟨20653320279611410571288243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13768880186407607047525495 20653320279611410571288243)
            ·
              refine ⟨30979980419417115856932365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20653320279611410571288243 30979980419417115856932365)
              ·
                refine ⟨11617492657281418446349637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 30979980419417115856932365 11617492657281418446349637)
                ·
                  refine ⟨2178279873240265958690557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11617492657281418446349637 2178279873240265958690557)
                  ·
                    refine ⟨816854952465099734508959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178279873240265958690557 816854952465099734508959)
                    ·
                      rfl

theorem cell22_2386229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 3].length) (baseStart_2386229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386229 prefixEnd_2386229 := by exact prefixLift 2386229
  have htrace : WordTrace (prefixWord ++ tailWord_2386229) baseStart_2386229 baseEnd_2386229 := by
    simpa [prefixWord, tailWord_2386229, baseEnd_2386229] using wordTrace_append hprefix tailTrace_2386229
  have hstable : (prefixWord ++ tailWord_2386229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386229).length < 2 ^ (prefixWord ++ tailWord_2386229).sum := by decide
  have hdescent : baseEnd_2386229 < baseStart_2386229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386261 : List Nat := [1, 3, 2, 2, 4, 1, 2, 1, 2, 4]
def baseStart_2386261 : Nat := 118140960795 + 2386261 * 2 ^ 59
def prefixEnd_2386261 : Nat := 4983230072969 + 3 ^ 40 * 2386261 * 2
def baseEnd_2386261 : Nat := 816865906719062317708861

theorem tailTrace_2386261 : CollatzResearch.WordTrace tailWord_2386261 prefixEnd_2386261 816865906719062317708861 := by
  unfold tailWord_2386261
  simp only [CollatzResearch.WordTrace]
  refine ⟨87034088807991412777918637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58022725871994275185279091 87034088807991412777918637)
  ·
    refine ⟨32637783302996779791719489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87034088807991412777918637 32637783302996779791719489)
    ·
      refine ⟨24478337477247584843789617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32637783302996779791719489 24478337477247584843789617)
      ·
        refine ⟨18358753107935688632842213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24478337477247584843789617 18358753107935688632842213)
        ·
          refine ⟨3442266207737941618657915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18358753107935688632842213 3442266207737941618657915)
          ·
            refine ⟨5163399311606912427986873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442266207737941618657915 5163399311606912427986873)
            ·
              refine ⟨3872549483705184320990155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5163399311606912427986873 3872549483705184320990155)
              ·
                refine ⟨5808824225557776481485233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3872549483705184320990155 5808824225557776481485233)
                ·
                  refine ⟨4356618169168332361113925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5808824225557776481485233 4356618169168332361113925)
                  ·
                    refine ⟨816865906719062317708861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4356618169168332361113925 816865906719062317708861)
                    ·
                      rfl

theorem cell22_2386261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 1, 2, 4].length) (baseStart_2386261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386261 prefixEnd_2386261 := by exact prefixLift 2386261
  have htrace : WordTrace (prefixWord ++ tailWord_2386261) baseStart_2386261 baseEnd_2386261 := by
    simpa [prefixWord, tailWord_2386261, baseEnd_2386261] using wordTrace_append hprefix tailTrace_2386261
  have hstable : (prefixWord ++ tailWord_2386261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386261).length < 2 ^ (prefixWord ++ tailWord_2386261).sum := by decide
  have hdescent : baseEnd_2386261 < baseStart_2386261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386291 : List Nat := [1, 1, 1, 2, 2, 1, 2, 8, 1, 3]
def baseStart_2386291 : Nat := 118140960795 + 2386291 * 2 ^ 59
def prefixEnd_2386291 : Nat := 4983230072969 + 3 ^ 40 * 2386291 * 2
def baseEnd_2386291 : Nat := 816876176332152239458769

theorem tailTrace_2386291 : CollatzResearch.WordTrace tailWord_2386291 prefixEnd_2386291 816876176332152239458769 := by
  unfold tailWord_2386291
  simp only [CollatzResearch.WordTrace]
  refine ⟨87035182997882727901510727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58023455331921818601007151 87035182997882727901510727)
  ·
    refine ⟨130552774496824091852266091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87035182997882727901510727 130552774496824091852266091)
    ·
      refine ⟨195829161745236137778399137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130552774496824091852266091 195829161745236137778399137)
      ·
        refine ⟨146871871308927103333799353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195829161745236137778399137 146871871308927103333799353)
        ·
          refine ⟨110153903481695327500349515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146871871308927103333799353 110153903481695327500349515)
          ·
            refine ⟨165230855222542991250524273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110153903481695327500349515 165230855222542991250524273)
            ·
              refine ⟨123923141416907243437893205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 165230855222542991250524273 123923141416907243437893205)
              ·
                refine ⟨1452224313479381759037811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 123923141416907243437893205 1452224313479381759037811)
                ·
                  refine ⟨2178336470219072638556717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452224313479381759037811 2178336470219072638556717)
                  ·
                    refine ⟨816876176332152239458769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178336470219072638556717 816876176332152239458769)
                    ·
                      rfl

theorem cell22_2386291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 8, 1, 3].length) (baseStart_2386291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386291 prefixEnd_2386291 := by exact prefixLift 2386291
  have htrace : WordTrace (prefixWord ++ tailWord_2386291) baseStart_2386291 baseEnd_2386291 := by
    simpa [prefixWord, tailWord_2386291, baseEnd_2386291] using wordTrace_append hprefix tailTrace_2386291
  have hstable : (prefixWord ++ tailWord_2386291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386291).length < 2 ^ (prefixWord ++ tailWord_2386291).sum := by decide
  have hdescent : baseEnd_2386291 < baseStart_2386291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386379 : List Nat := [1, 1, 1, 1, 3, 3, 1, 5, 2, 4]
def baseStart_2386379 : Nat := 118140960795 + 2386379 * 2 ^ 59
def prefixEnd_2386379 : Nat := 4983230072969 + 3 ^ 40 * 2386379 * 2
def baseEnd_2386379 : Nat := 816906300530549343258499

theorem tailTrace_2386379 : CollatzResearch.WordTrace tailWord_2386379 prefixEnd_2386379 816906300530549343258499 := by
  unfold tailWord_2386379
  simp only [CollatzResearch.WordTrace]
  refine ⟨87038392621563918930714191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58025595081042612620476127 87038392621563918930714191)
  ·
    refine ⟨130557588932345878396071287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87038392621563918930714191 130557588932345878396071287)
    ·
      refine ⟨195836383398518817594106931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130557588932345878396071287 195836383398518817594106931)
      ·
        refine ⟨293754575097778226391160397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195836383398518817594106931 293754575097778226391160397)
        ·
          refine ⟨110157965661666834896685149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293754575097778226391160397 110157965661666834896685149)
          ·
            refine ⟨41309237123125063086256931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110157965661666834896685149 41309237123125063086256931)
            ·
              refine ⟨61963855684687594629385397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41309237123125063086256931 61963855684687594629385397)
              ·
                refine ⟨5809111470439461996504881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 61963855684687594629385397 5809111470439461996504881)
                ·
                  refine ⟨4356833602829596497378661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5809111470439461996504881 4356833602829596497378661)
                  ·
                    refine ⟨816906300530549343258499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4356833602829596497378661 816906300530549343258499)
                    ·
                      rfl

theorem cell22_2386379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 4].length) (baseStart_2386379 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386379 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386379 prefixEnd_2386379 := by exact prefixLift 2386379
  have htrace : WordTrace (prefixWord ++ tailWord_2386379) baseStart_2386379 baseEnd_2386379 := by
    simpa [prefixWord, tailWord_2386379, baseEnd_2386379] using wordTrace_append hprefix tailTrace_2386379
  have hstable : (prefixWord ++ tailWord_2386379).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386379).length < 2 ^ (prefixWord ++ tailWord_2386379).sum := by decide
  have hdescent : baseEnd_2386379 < baseStart_2386379 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386456 : List Nat := [2, 1, 2, 3, 3, 1, 1, 4, 5]
def baseStart_2386456 : Nat := 118140960795 + 2386456 * 2 ^ 59
def prefixEnd_2386456 : Nat := 4983230072969 + 3 ^ 40 * 2386456 * 2
def baseEnd_2386456 : Nat := 272310886401382269694421

theorem tailTrace_2386456 : CollatzResearch.WordTrace tailWord_2386456 prefixEnd_2386456 272310886401382269694421 := by
  unfold tailWord_2386456
  simp only [CollatzResearch.WordTrace]
  refine ⟨43520600521142480540633611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58027467361523307387511481 43520600521142480540633611)
  ·
    refine ⟨65280900781713720810950417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43520600521142480540633611 65280900781713720810950417)
    ·
      refine ⟨48960675586285290608212813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65280900781713720810950417 48960675586285290608212813)
      ·
        refine ⟨18360253344856983978079805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 48960675586285290608212813 18360253344856983978079805)
        ·
          refine ⟨6885095004321368991779927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18360253344856983978079805 6885095004321368991779927)
          ·
            refine ⟨10327642506482053487669891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6885095004321368991779927 10327642506482053487669891)
            ·
              refine ⟨15491463759723080231504837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10327642506482053487669891 15491463759723080231504837)
              ·
                refine ⟨2904649454948077543407157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15491463759723080231504837 2904649454948077543407157)
                ·
                  refine ⟨272310886401382269694421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2904649454948077543407157 272310886401382269694421)
                  ·
                    rfl

theorem cell22_2386456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 4, 5].length) (baseStart_2386456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386456 prefixEnd_2386456 := by exact prefixLift 2386456
  have htrace : WordTrace (prefixWord ++ tailWord_2386456) baseStart_2386456 baseEnd_2386456 := by
    simpa [prefixWord, tailWord_2386456, baseEnd_2386456] using wordTrace_append hprefix tailTrace_2386456
  have hstable : (prefixWord ++ tailWord_2386456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386456).length < 2 ^ (prefixWord ++ tailWord_2386456).sum := by decide
  have hdescent : baseEnd_2386456 < baseStart_2386456 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386460 : List Nat := [2, 2, 3, 1, 2, 3, 1, 4, 1, 3]
def baseStart_2386460 : Nat := 118140960795 + 2386460 * 2 ^ 59
def prefixEnd_2386460 : Nat := 4983230072969 + 3 ^ 40 * 2386460 * 2
def baseEnd_2386460 : Nat := 816934028485892131983251

theorem tailTrace_2386460 : CollatzResearch.WordTrace tailWord_2386460 prefixEnd_2386460 816934028485892131983251 := by
  unfold tailWord_2386460
  simp only [CollatzResearch.WordTrace]
  refine ⟨43520673467135234882206417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58027564622846979842941889 43520673467135234882206417)
  ·
    refine ⟨32640505100351426161654813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43520673467135234882206417 32640505100351426161654813)
    ·
      refine ⟨12240189412631784810620555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32640505100351426161654813 12240189412631784810620555)
      ·
        refine ⟨18360284118947677215930833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12240189412631784810620555 18360284118947677215930833)
        ·
          refine ⟨13770213089210757911948125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18360284118947677215930833 13770213089210757911948125)
          ·
            refine ⟨5163829908454034216980547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13770213089210757911948125 5163829908454034216980547)
            ·
              refine ⟨7745744862681051325470821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163829908454034216980547 7745744862681051325470821)
              ·
                refine ⟨1452327161752697123525779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7745744862681051325470821 1452327161752697123525779)
                ·
                  refine ⟨2178490742629045685288669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452327161752697123525779 2178490742629045685288669)
                  ·
                    refine ⟨816934028485892131983251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178490742629045685288669 816934028485892131983251)
                    ·
                      rfl

theorem cell22_2386460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_2386460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386460 prefixEnd_2386460 := by exact prefixLift 2386460
  have htrace : WordTrace (prefixWord ++ tailWord_2386460) baseStart_2386460 baseEnd_2386460 := by
    simpa [prefixWord, tailWord_2386460, baseEnd_2386460] using wordTrace_append hprefix tailTrace_2386460
  have hstable : (prefixWord ++ tailWord_2386460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386460).length < 2 ^ (prefixWord ++ tailWord_2386460).sum := by decide
  have hdescent : baseEnd_2386460 < baseStart_2386460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386494 : List Nat := [4, 2, 1, 4, 1, 1, 2, 3, 1, 3]
def baseStart_2386494 : Nat := 118140960795 + 2386494 * 2 ^ 59
def prefixEnd_2386494 : Nat := 4983230072969 + 3 ^ 40 * 2386494 * 2
def baseEnd_2386494 : Nat := 816945667380727376633147

theorem tailTrace_2386494 : CollatzResearch.WordTrace tailWord_2386494 prefixEnd_2386494 816945667380727376633147 := by
  unfold tailWord_2386494
  simp only [CollatzResearch.WordTrace]
  refine ⟨10880323377018411696393817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58028391344098195714100357 10880323377018411696393817)
  ·
    refine ⟨8160242532763808772295363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10880323377018411696393817 8160242532763808772295363)
    ·
      refine ⟨12240363799145713158443045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8160242532763808772295363 12240363799145713158443045)
      ·
        refine ⟨2295068212339821217208071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12240363799145713158443045 2295068212339821217208071)
        ·
          refine ⟨3442602318509731825812107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295068212339821217208071 3442602318509731825812107)
          ·
            refine ⟨5163903477764597738718161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3442602318509731825812107 5163903477764597738718161)
            ·
              refine ⟨3872927608323448304038621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5163903477764597738718161 3872927608323448304038621)
              ·
                refine ⟨1452347853121293114014483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3872927608323448304038621 1452347853121293114014483)
                ·
                  refine ⟨2178521779681939671021725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452347853121293114014483 2178521779681939671021725)
                  ·
                    refine ⟨816945667380727376633147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178521779681939671021725 816945667380727376633147)
                    ·
                      rfl

theorem cell22_2386494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 3, 1, 3].length) (baseStart_2386494 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386494 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386494 prefixEnd_2386494 := by exact prefixLift 2386494
  have htrace : WordTrace (prefixWord ++ tailWord_2386494) baseStart_2386494 baseEnd_2386494 := by
    simpa [prefixWord, tailWord_2386494, baseEnd_2386494] using wordTrace_append hprefix tailTrace_2386494
  have hstable : (prefixWord ++ tailWord_2386494).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386494).length < 2 ^ (prefixWord ++ tailWord_2386494).sum := by decide
  have hdescent : baseEnd_2386494 < baseStart_2386494 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386503 : List Nat := [1, 1, 4, 1, 4, 2, 1, 3, 1, 4]
def baseStart_2386503 : Nat := 118140960795 + 2386503 * 2 ^ 59
def prefixEnd_2386503 : Nat := 4983230072969 + 3 ^ 40 * 2386503 * 2
def baseEnd_2386503 : Nat := 816948748264654353158119

theorem tailTrace_2386503 : CollatzResearch.WordTrace tailWord_2386503 prefixEnd_2386503 816948748264654353158119 := by
  unfold tailWord_2386503
  simp only [CollatzResearch.WordTrace]
  refine ⟨87042915273114688108228163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58028610182076458738818775 87042915273114688108228163)
  ·
    refine ⟨130564372909672032162342245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87042915273114688108228163 130564372909672032162342245)
    ·
      refine ⟨24480819920563506030439171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130564372909672032162342245 24480819920563506030439171)
      ·
        refine ⟨36721229880845259045658757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24480819920563506030439171 36721229880845259045658757)
        ·
          refine ⟨6885230602658486071061017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36721229880845259045658757 6885230602658486071061017)
          ·
            refine ⟨5163922951993864553295763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6885230602658486071061017 5163922951993864553295763)
            ·
              refine ⟨7745884427990796829943645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5163922951993864553295763 7745884427990796829943645)
              ·
                refine ⟨2904706660496548811228867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7745884427990796829943645 2904706660496548811228867)
                ·
                  refine ⟨4357059990744823216843301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2904706660496548811228867 4357059990744823216843301)
                  ·
                    refine ⟨816948748264654353158119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4357059990744823216843301 816948748264654353158119)
                    ·
                      rfl

theorem cell22_2386503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_2386503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386503 prefixEnd_2386503 := by exact prefixLift 2386503
  have htrace : WordTrace (prefixWord ++ tailWord_2386503) baseStart_2386503 baseEnd_2386503 := by
    simpa [prefixWord, tailWord_2386503, baseEnd_2386503] using wordTrace_append hprefix tailTrace_2386503
  have hstable : (prefixWord ++ tailWord_2386503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386503).length < 2 ^ (prefixWord ++ tailWord_2386503).sum := by decide
  have hdescent : baseEnd_2386503 < baseStart_2386503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386638 : List Nat := [4, 1, 1, 1, 3, 2, 1, 2, 3, 4]
def baseStart_2386638 : Nat := 118140960795 + 2386638 * 2 ^ 59
def prefixEnd_2386638 : Nat := 4983230072969 + 3 ^ 40 * 2386638 * 2
def baseEnd_2386638 : Nat := 816994961523559001032705

theorem tailTrace_2386638 : CollatzResearch.WordTrace tailWord_2386638 prefixEnd_2386638 816994961523559001032705 := by
  unfold tailWord_2386638
  simp only [CollatzResearch.WordTrace]
  refine ⟨10880979890953200770549071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58031892751750404109595045 10880979890953200770549071)
  ·
    refine ⟨16321469836429801155823607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10880979890953200770549071 16321469836429801155823607)
    ·
      refine ⟨24482204754644701733735411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16321469836429801155823607 24482204754644701733735411)
      ·
        refine ⟨36723307131967052600603117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24482204754644701733735411 36723307131967052600603117)
        ·
          refine ⟨13771240174487644725226169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36723307131967052600603117 13771240174487644725226169)
          ·
            refine ⟨10328430130865733543919627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13771240174487644725226169 10328430130865733543919627)
            ·
              refine ⟨15492645196298600315879441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10328430130865733543919627 15492645196298600315879441)
              ·
                refine ⟨11619483897223950236909581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15492645196298600315879441 11619483897223950236909581)
                ·
                  refine ⟨4357306461458981338841093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11619483897223950236909581 4357306461458981338841093)
                  ·
                    refine ⟨816994961523559001032705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4357306461458981338841093 816994961523559001032705)
                    ·
                      rfl

theorem cell22_2386638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 2, 3, 4].length) (baseStart_2386638 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386638 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386638 prefixEnd_2386638 := by exact prefixLift 2386638
  have htrace : WordTrace (prefixWord ++ tailWord_2386638) baseStart_2386638 baseEnd_2386638 := by
    simpa [prefixWord, tailWord_2386638, baseEnd_2386638] using wordTrace_append hprefix tailTrace_2386638
  have hstable : (prefixWord ++ tailWord_2386638).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386638).length < 2 ^ (prefixWord ++ tailWord_2386638).sum := by decide
  have hdescent : baseEnd_2386638 < baseStart_2386638 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386668 : List Nat := [2, 2, 1, 1, 2, 2, 1, 4, 4, 3]
def baseStart_2386668 : Nat := 118140960795 + 2386668 * 2 ^ 59
def prefixEnd_2386668 : Nat := 4983230072969 + 3 ^ 40 * 2386668 * 2
def baseEnd_2386668 : Nat := 817005231136648922782613

theorem tailTrace_2386668 : CollatzResearch.WordTrace tailWord_2386668 prefixEnd_2386668 817005231136648922782613 := by
  unfold tailWord_2386668
  simp only [CollatzResearch.WordTrace]
  refine ⟨43524466658758460643992329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58032622211677947525323105 43524466658758460643992329)
  ·
    refine ⟨32643349994068845482994247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43524466658758460643992329 32643349994068845482994247)
    ·
      refine ⟨48965024991103268224491371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32643349994068845482994247 48965024991103268224491371)
      ·
        refine ⟨73447537486654902336737057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48965024991103268224491371 73447537486654902336737057)
        ·
          refine ⟨55085653114991176752552793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73447537486654902336737057 55085653114991176752552793)
          ·
            refine ⟨41314239836243382564414595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55085653114991176752552793 41314239836243382564414595)
            ·
              refine ⟨61971359754365073846621893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41314239836243382564414595 61971359754365073846621893)
              ·
                refine ⟨11619629953943451346241605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 61971359754365073846621893 11619629953943451346241605)
                ·
                  refine ⟨2178680616364397127420301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11619629953943451346241605 2178680616364397127420301)
                  ·
                    refine ⟨817005231136648922782613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178680616364397127420301 817005231136648922782613)
                    ·
                      rfl

theorem cell22_2386668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 4, 3].length) (baseStart_2386668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386668 prefixEnd_2386668 := by exact prefixLift 2386668
  have htrace : WordTrace (prefixWord ++ tailWord_2386668) baseStart_2386668 baseEnd_2386668 := by
    simpa [prefixWord, tailWord_2386668, baseEnd_2386668] using wordTrace_append hprefix tailTrace_2386668
  have hstable : (prefixWord ++ tailWord_2386668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386668).length < 2 ^ (prefixWord ++ tailWord_2386668).sum := by decide
  have hdescent : baseEnd_2386668 < baseStart_2386668 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386670 : List Nat := [4, 1, 2, 1, 1, 3, 1, 5, 4]
def baseStart_2386670 : Nat := 118140960795 + 2386670 * 2 ^ 59
def prefixEnd_2386670 : Nat := 4983230072969 + 3 ^ 40 * 2386670 * 2
def baseEnd_2386670 : Nat := 272335305259173861410869

theorem tailTrace_2386670 : CollatzResearch.WordTrace tailWord_2386670 prefixEnd_2386670 272335305259173861410869 := by
  unfold tailWord_2386670
  simp only [CollatzResearch.WordTrace]
  refine ⟨10881125782938709453694683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58032670842339783753038309 10881125782938709453694683)
  ·
    refine ⟨16321688674408064180542025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10881125782938709453694683 16321688674408064180542025)
    ·
      refine ⟨12241266505806048135406519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16321688674408064180542025 12241266505806048135406519)
      ·
        refine ⟨18361899758709072203109779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12241266505806048135406519 18361899758709072203109779)
        ·
          refine ⟨27542849638063608304664669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18361899758709072203109779 27542849638063608304664669)
          ·
            refine ⟨10328568614273853114249251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27542849638063608304664669 10328568614273853114249251)
            ·
              refine ⟨15492852921410779671373877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10328568614273853114249251 15492852921410779671373877)
              ·
                refine ⟨1452454961382260594191301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 15492852921410779671373877 1452454961382260594191301)
                ·
                  refine ⟨272335305259173861410869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1452454961382260594191301 272335305259173861410869)
                  ·
                    rfl

theorem cell22_2386670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_2386670 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386670 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386670 prefixEnd_2386670 := by exact prefixLift 2386670
  have htrace : WordTrace (prefixWord ++ tailWord_2386670) baseStart_2386670 baseEnd_2386670 := by
    simpa [prefixWord, tailWord_2386670, baseEnd_2386670] using wordTrace_append hprefix tailTrace_2386670
  have hstable : (prefixWord ++ tailWord_2386670).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386670).length < 2 ^ (prefixWord ++ tailWord_2386670).sum := by decide
  have hdescent : baseEnd_2386670 < baseStart_2386670 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386676 : List Nat := [2, 6, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2386676 : Nat := 118140960795 + 2386676 * 2 ^ 59
def prefixEnd_2386676 : Nat := 4983230072969 + 3 ^ 40 * 2386676 * 2
def baseEnd_2386676 : Nat := 272335989900046522860863

theorem tailTrace_2386676 : CollatzResearch.WordTrace tailWord_2386676 prefixEnd_2386676 272335989900046522860863 := by
  unfold tailWord_2386676
  simp only [CollatzResearch.WordTrace]
  refine ⟨43524612550743969327137941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58032816734325292436183921 43524612550743969327137941)
  ·
    refine ⟨2040216213316123562209591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43524612550743969327137941 2040216213316123562209591)
    ·
      refine ⟨3060324319974185343314387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2040216213316123562209591 3060324319974185343314387)
      ·
        refine ⟨4590486479961278014971581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3060324319974185343314387 4590486479961278014971581)
        ·
          refine ⟨1721432429985479255614343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4590486479961278014971581 1721432429985479255614343)
          ·
            refine ⟨2582148644978218883421515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721432429985479255614343 2582148644978218883421515)
            ·
              refine ⟨3873222967467328325132273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582148644978218883421515 3873222967467328325132273)
              ·
                refine ⟨2904917225600496243849205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3873222967467328325132273 2904917225600496243849205)
                ·
                  refine ⟨272335989900046522860863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2904917225600496243849205 272335989900046522860863)
                  ·
                    rfl

theorem cell22_2386676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2386676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386676 prefixEnd_2386676 := by exact prefixLift 2386676
  have htrace : WordTrace (prefixWord ++ tailWord_2386676) baseStart_2386676 baseEnd_2386676 := by
    simpa [prefixWord, tailWord_2386676, baseEnd_2386676] using wordTrace_append hprefix tailTrace_2386676
  have hstable : (prefixWord ++ tailWord_2386676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386676).length < 2 ^ (prefixWord ++ tailWord_2386676).sum := by decide
  have hdescent : baseEnd_2386676 < baseStart_2386676 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386713 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 5, 3]
def baseStart_2386713 : Nat := 118140960795 + 2386713 * 2 ^ 59
def prefixEnd_2386713 : Nat := 4983230072969 + 3 ^ 40 * 2386713 * 2
def baseEnd_2386713 : Nat := 817020635556283805407475

theorem tailTrace_2386713 : CollatzResearch.WordTrace tailWord_2386713 prefixEnd_2386713 817020635556283805407475 := by
  unfold tailWord_2386713
  simp only [CollatzResearch.WordTrace]
  refine ⟨87050574602353893973372793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58033716401569262648915195 87050574602353893973372793)
  ·
    refine ⟨65287930951765420480029595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87050574602353893973372793 65287930951765420480029595)
    ·
      refine ⟨97931896427648130720044393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65287930951765420480029595 97931896427648130720044393)
      ·
        refine ⟨73448922320736098040033295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97931896427648130720044393 73448922320736098040033295)
        ·
          refine ⟨110173383481104147060049943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73448922320736098040033295 110173383481104147060049943)
          ·
            refine ⟨165260075221656220590074915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110173383481104147060049943 165260075221656220590074915)
            ·
              refine ⟨247890112832484330885112373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165260075221656220590074915 247890112832484330885112373)
              ·
                refine ⟨23239698078045406020479285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 247890112832484330885112373 23239698078045406020479285)
                ·
                  refine ⟨2178721694816756814419933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23239698078045406020479285 2178721694816756814419933)
                  ·
                    refine ⟨817020635556283805407475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178721694816756814419933 817020635556283805407475)
                    ·
                      rfl

theorem cell22_2386713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 3].length) (baseStart_2386713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386713 prefixEnd_2386713 := by exact prefixLift 2386713
  have htrace : WordTrace (prefixWord ++ tailWord_2386713) baseStart_2386713 baseEnd_2386713 := by
    simpa [prefixWord, tailWord_2386713, baseEnd_2386713] using wordTrace_append hprefix tailTrace_2386713
  have hstable : (prefixWord ++ tailWord_2386713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386713).length < 2 ^ (prefixWord ++ tailWord_2386713).sum := by decide
  have hdescent : baseEnd_2386713 < baseStart_2386713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386743 : List Nat := [1, 1, 3, 1, 2, 1, 4, 4, 5]
def baseStart_2386743 : Nat := 118140960795 + 2386743 * 2 ^ 59
def prefixEnd_2386743 : Nat := 4983230072969 + 3 ^ 40 * 2386743 * 2
def baseEnd_2386743 : Nat := 272343635056457909052461

theorem tailTrace_2386743 : CollatzResearch.WordTrace tailWord_2386743 prefixEnd_2386743 272343635056457909052461 := by
  unfold tailWord_2386743
  simp only [CollatzResearch.WordTrace]
  refine ⟨87051668792245209096964883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58034445861496806064643255 87051668792245209096964883)
  ·
    refine ⟨130577503188367813645447325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87051668792245209096964883 130577503188367813645447325)
    ·
      refine ⟨48966563695637930117042747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130577503188367813645447325 48966563695637930117042747)
      ·
        refine ⟨73449845543456895175564121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48966563695637930117042747 73449845543456895175564121)
        ·
          refine ⟨55087384157592671381673091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73449845543456895175564121 55087384157592671381673091)
          ·
            refine ⟨82631076236389007072509637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55087384157592671381673091 82631076236389007072509637)
            ·
              refine ⟨15493326794322938826095557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82631076236389007072509637 15493326794322938826095557)
              ·
                refine ⟨2904998773935551029892917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15493326794322938826095557 2904998773935551029892917)
                ·
                  refine ⟨272343635056457909052461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2904998773935551029892917 272343635056457909052461)
                  ·
                    rfl

theorem cell22_2386743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 4, 5].length) (baseStart_2386743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386743 prefixEnd_2386743 := by exact prefixLift 2386743
  have htrace : WordTrace (prefixWord ++ tailWord_2386743) baseStart_2386743 baseEnd_2386743 := by
    simpa [prefixWord, tailWord_2386743, baseEnd_2386743] using wordTrace_append hprefix tailTrace_2386743
  have hstable : (prefixWord ++ tailWord_2386743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386743).length < 2 ^ (prefixWord ++ tailWord_2386743).sum := by decide
  have hdescent : baseEnd_2386743 < baseStart_2386743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386753 : List Nat := [1, 2, 5, 3, 2, 1, 2, 1, 2, 3]
def baseStart_2386753 : Nat := 118140960795 + 2386753 * 2 ^ 59
def prefixEnd_2386753 : Nat := 4983230072969 + 3 ^ 40 * 2386753 * 2
def baseEnd_2386753 : Nat := 817034328373737034407353

theorem tailTrace_2386753 : CollatzResearch.WordTrace tailWord_2386753 prefixEnd_2386753 817034328373737034407353 := by
  unfold tailWord_2386753
  simp only [CollatzResearch.WordTrace]
  refine ⟨87052033522208980804828913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58034689014805987203219275 87052033522208980804828913)
  ·
    refine ⟨65289025141656735603621685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87052033522208980804828913 65289025141656735603621685)
    ·
      refine ⟨6120846107030318962839533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 65289025141656735603621685 6120846107030318962839533)
      ·
        refine ⟨2295317290136369611064825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6120846107030318962839533 2295317290136369611064825)
        ·
          refine ⟨1721487967602277208298619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2295317290136369611064825 1721487967602277208298619)
          ·
            refine ⟨2582231951403415812447929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721487967602277208298619 2582231951403415812447929)
            ·
              refine ⟨1936673963552561859335947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2582231951403415812447929 1936673963552561859335947)
              ·
                refine ⟨2905010945328842789003921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1936673963552561859335947 2905010945328842789003921)
                ·
                  refine ⟨2178758208996632091752941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2905010945328842789003921 2178758208996632091752941)
                  ·
                    refine ⟨817034328373737034407353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178758208996632091752941 817034328373737034407353)
                    ·
                      rfl

theorem cell22_2386753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_2386753 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386753 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386753 prefixEnd_2386753 := by exact prefixLift 2386753
  have htrace : WordTrace (prefixWord ++ tailWord_2386753) baseStart_2386753 baseEnd_2386753 := by
    simpa [prefixWord, tailWord_2386753, baseEnd_2386753] using wordTrace_append hprefix tailTrace_2386753
  have hstable : (prefixWord ++ tailWord_2386753).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386753).length < 2 ^ (prefixWord ++ tailWord_2386753).sum := by decide
  have hdescent : baseEnd_2386753 < baseStart_2386753 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386798 : List Nat := [4, 1, 2, 3, 2, 2, 2, 2, 1, 3]
def baseStart_2386798 : Nat := 118140960795 + 2386798 * 2 ^ 59
def prefixEnd_2386798 : Nat := 4983230072969 + 3 ^ 40 * 2386798 * 2
def baseEnd_2386798 : Nat := 817049732793371917032215

theorem tailTrace_2386798 : CollatzResearch.WordTrace tailWord_2386798 prefixEnd_2386798 817049732793371917032215 := by
  unfold tailWord_2386798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10881709350880744186277131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58035783204697302326811365 10881709350880744186277131)
  ·
    refine ⟨16322564026321116279415697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10881709350880744186277131 16322564026321116279415697)
    ·
      refine ⟨12241923019740837209561773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16322564026321116279415697 12241923019740837209561773)
      ·
        refine ⟨4590721132402813953585665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12241923019740837209561773 4590721132402813953585665)
        ·
          refine ⟨3443040849302110465189249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4590721132402813953585665 3443040849302110465189249)
          ·
            refine ⟨2582280636976582848891937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3443040849302110465189249 2582280636976582848891937)
            ·
              refine ⟨1936710477732437136668953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2582280636976582848891937 1936710477732437136668953)
              ·
                refine ⟨1452532858299327852501715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1936710477732437136668953 1452532858299327852501715)
                ·
                  refine ⟨2178799287448991778752573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452532858299327852501715 2178799287448991778752573)
                  ·
                    refine ⟨817049732793371917032215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178799287448991778752573 817049732793371917032215)
                    ·
                      rfl

theorem cell22_2386798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_2386798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386798 prefixEnd_2386798 := by exact prefixLift 2386798
  have htrace : WordTrace (prefixWord ++ tailWord_2386798) baseStart_2386798 baseEnd_2386798 := by
    simpa [prefixWord, tailWord_2386798, baseEnd_2386798] using wordTrace_append hprefix tailTrace_2386798
  have hstable : (prefixWord ++ tailWord_2386798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386798).length < 2 ^ (prefixWord ++ tailWord_2386798).sum := by decide
  have hdescent : baseEnd_2386798 < baseStart_2386798 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386820 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 6, 3]
def baseStart_2386820 : Nat := 118140960795 + 2386820 * 2 ^ 59
def prefixEnd_2386820 : Nat := 4983230072969 + 3 ^ 40 * 2386820 * 2
def baseEnd_2386820 : Nat := 817057263842971192982147

theorem tailTrace_2386820 : CollatzResearch.WordTrace tailWord_2386820 prefixEnd_2386820 817057263842971192982147 := by
  unfold tailWord_2386820
  simp only [CollatzResearch.WordTrace]
  refine ⟨43527238606483125623758957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58036318141977500831678609 43527238606483125623758957)
  ·
    refine ⟨16322714477431172108909609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43527238606483125623758957 16322714477431172108909609)
    ·
      refine ⟨12242035858073379081682207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16322714477431172108909609 12242035858073379081682207)
      ·
        refine ⟨18363053787110068622523311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12242035858073379081682207 18363053787110068622523311)
        ·
          refine ⟨27544580680665102933784967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18363053787110068622523311 27544580680665102933784967)
          ·
            refine ⟨41316871020997654400677451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27544580680665102933784967 41316871020997654400677451)
            ·
              refine ⟨61975306531496481601016177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41316871020997654400677451 61975306531496481601016177)
              ·
                refine ⟨46481479898622361200762133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 61975306531496481601016177 46481479898622361200762133)
                ·
                  refine ⟨2178819370247923181285725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46481479898622361200762133 2178819370247923181285725)
                  ·
                    refine ⟨817057263842971192982147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2178819370247923181285725 817057263842971192982147)
                    ·
                      rfl

theorem cell22_2386820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 6, 3].length) (baseStart_2386820 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386820 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386820 prefixEnd_2386820 := by exact prefixLift 2386820
  have htrace : WordTrace (prefixWord ++ tailWord_2386820) baseStart_2386820 baseEnd_2386820 := by
    simpa [prefixWord, tailWord_2386820, baseEnd_2386820] using wordTrace_append hprefix tailTrace_2386820
  have hstable : (prefixWord ++ tailWord_2386820).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386820).length < 2 ^ (prefixWord ++ tailWord_2386820).sum := by decide
  have hdescent : baseEnd_2386820 < baseStart_2386820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386850 : List Nat := [3, 3, 1, 2, 2, 2, 9]
def baseStart_2386850 : Nat := 118140960795 + 2386850 * 2 ^ 59
def prefixEnd_2386850 : Nat := 4983230072969 + 3 ^ 40 * 2386850 * 2
def baseEnd_2386850 : Nat := 30261760498372633878965

theorem tailTrace_2386850 : CollatzResearch.WordTrace tailWord_2386850 prefixEnd_2386850 30261760498372633878965 := by
  unfold tailWord_2386850
  simp only [CollatzResearch.WordTrace]
  refine ⟨21763892850714391592777501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58037047601905044247406669 21763892850714391592777501)
  ·
    refine ⟨8161459819017896847291563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21763892850714391592777501 8161459819017896847291563)
    ·
      refine ⟨12242189728526845270937345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8161459819017896847291563 12242189728526845270937345)
      ·
        refine ⟨9181642296395133953203009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12242189728526845270937345 9181642296395133953203009)
        ·
          refine ⟨6886231722296350464902257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9181642296395133953203009 6886231722296350464902257)
          ·
            refine ⟨5164673791722262848676693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6886231722296350464902257 5164673791722262848676693)
            ·
              refine ⟨30261760498372633878965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5164673791722262848676693 30261760498372633878965)
              ·
                rfl

theorem cell22_2386850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 9].length) (baseStart_2386850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386850 prefixEnd_2386850 := by exact prefixLift 2386850
  have htrace : WordTrace (prefixWord ++ tailWord_2386850) baseStart_2386850 baseEnd_2386850 := by
    simpa [prefixWord, tailWord_2386850, baseEnd_2386850] using wordTrace_append hprefix tailTrace_2386850
  have hstable : (prefixWord ++ tailWord_2386850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386850).length < 2 ^ (prefixWord ++ tailWord_2386850).sum := by decide
  have hdescent : baseEnd_2386850 < baseStart_2386850 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386863 : List Nat := [1, 1, 2, 1, 2, 2, 2, 3, 2, 6]
def baseStart_2386863 : Nat := 118140960795 + 2386863 * 2 ^ 59
def prefixEnd_2386863 : Nat := 4983230072969 + 3 ^ 40 * 2386863 * 2
def baseEnd_2386863 : Nat := 817071983621733414157015

theorem tailTrace_2386863 : CollatzResearch.WordTrace tailWord_2386863 prefixEnd_2386863 817071983621733414157015 := by
  unfold tailWord_2386863
  simp only [CollatzResearch.WordTrace]
  refine ⟨87056045551810469591333243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58037363701206979727555495 87056045551810469591333243)
  ·
    refine ⟨130584068327715704386999865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87056045551810469591333243 130584068327715704386999865)
    ·
      refine ⟨97938051245786778290249899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130584068327715704386999865 97938051245786778290249899)
      ·
        refine ⟨146907076868680167435374849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97938051245786778290249899 146907076868680167435374849)
        ·
          refine ⟨110180307651510125576531137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146907076868680167435374849 110180307651510125576531137)
          ·
            refine ⟨82635230738632594182398353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110180307651510125576531137 82635230738632594182398353)
            ·
              refine ⟨61976423053974445636798765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82635230738632594182398353 61976423053974445636798765)
              ·
                refine ⟨23241158645240417113799537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 61976423053974445636798765 23241158645240417113799537)
                ·
                  refine ⟨17430868983930312835349653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23241158645240417113799537 17430868983930312835349653)
                  ·
                    refine ⟨817071983621733414157015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17430868983930312835349653 817071983621733414157015)
                    ·
                      rfl

theorem cell22_2386863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_2386863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386863 prefixEnd_2386863 := by exact prefixLift 2386863
  have htrace : WordTrace (prefixWord ++ tailWord_2386863) baseStart_2386863 baseEnd_2386863 := by
    simpa [prefixWord, tailWord_2386863, baseEnd_2386863] using wordTrace_append hprefix tailTrace_2386863
  have hstable : (prefixWord ++ tailWord_2386863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386863).length < 2 ^ (prefixWord ++ tailWord_2386863).sum := by decide
  have hdescent : baseEnd_2386863 < baseStart_2386863 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386929 : List Nat := [1, 2, 2, 2, 4, 3, 2, 1, 5]
def baseStart_2386929 : Nat := 118140960795 + 2386929 * 2 ^ 59
def prefixEnd_2386929 : Nat := 4983230072969 + 3 ^ 40 * 2386929 * 2
def baseEnd_2386929 : Nat := 272364858923510414002271

theorem tailTrace_2386929 : CollatzResearch.WordTrace tailWord_2386929 prefixEnd_2386929 272364858923510414002271 := by
  unfold tailWord_2386929
  simp only [CollatzResearch.WordTrace]
  refine ⟨87058452769571362863235841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58038968513047575242157227 87058452769571362863235841)
  ·
    refine ⟨65293839577178522147426881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87058452769571362863235841 65293839577178522147426881)
    ·
      refine ⟨48970379682883891610570161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65293839577178522147426881 48970379682883891610570161)
      ·
        refine ⟨36727784762162918707927621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48970379682883891610570161 36727784762162918707927621)
        ·
          refine ⟨6886459642905547257736429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36727784762162918707927621 6886459642905547257736429)
          ·
            refine ⟨2582422366089580221651161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6886459642905547257736429 2582422366089580221651161)
            ·
              refine ⟨1936816774567185166238371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2582422366089580221651161 1936816774567185166238371)
              ·
                refine ⟨2905225161850777749357557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1936816774567185166238371 2905225161850777749357557)
                ·
                  refine ⟨272364858923510414002271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2905225161850777749357557 272364858923510414002271)
                  ·
                    rfl

theorem cell22_2386929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 1, 5].length) (baseStart_2386929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386929 prefixEnd_2386929 := by exact prefixLift 2386929
  have htrace : WordTrace (prefixWord ++ tailWord_2386929) baseStart_2386929 baseEnd_2386929 := by
    simpa [prefixWord, tailWord_2386929, baseEnd_2386929] using wordTrace_append hprefix tailTrace_2386929
  have hstable : (prefixWord ++ tailWord_2386929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386929).length < 2 ^ (prefixWord ++ tailWord_2386929).sum := by decide
  have hdescent : baseEnd_2386929 < baseStart_2386929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2386955 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 3, 5]
def baseStart_2386955 : Nat := 118140960795 + 2386955 * 2 ^ 59
def prefixEnd_2386955 : Nat := 4983230072969 + 3 ^ 40 * 2386955 * 2
def baseEnd_2386955 : Nat := 817103477101875840856733

theorem tailTrace_2386955 : CollatzResearch.WordTrace tailWord_2386955 prefixEnd_2386955 817103477101875840856733 := by
  unfold tailWord_2386955
  simp only [CollatzResearch.WordTrace]
  refine ⟨87059401067477169303682319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58039600711651446202454879 87059401067477169303682319)
  ·
    refine ⟨130589101601215753955523479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87059401067477169303682319 130589101601215753955523479)
    ·
      refine ⟨195883652401823630933285219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130589101601215753955523479 195883652401823630933285219)
      ·
        refine ⟨293825478602735446399927829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195883652401823630933285219 293825478602735446399927829)
        ·
          refine ⟨13773069309503224049996617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 293825478602735446399927829 13773069309503224049996617)
          ·
            refine ⟨10329801982127418037497463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13773069309503224049996617 10329801982127418037497463)
            ·
              refine ⟨15494702973191127056246195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10329801982127418037497463 15494702973191127056246195)
              ·
                refine ⟨23242054459786690584369293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15494702973191127056246195 23242054459786690584369293)
                ·
                  refine ⟨8715770422420008969138485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23242054459786690584369293 8715770422420008969138485)
                  ·
                    refine ⟨817103477101875840856733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8715770422420008969138485 817103477101875840856733)
                    ·
                      rfl

theorem cell22_2386955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 3, 5].length) (baseStart_2386955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2386955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2386955 prefixEnd_2386955 := by exact prefixLift 2386955
  have htrace : WordTrace (prefixWord ++ tailWord_2386955) baseStart_2386955 baseEnd_2386955 := by
    simpa [prefixWord, tailWord_2386955, baseEnd_2386955] using wordTrace_append hprefix tailTrace_2386955
  have hstable : (prefixWord ++ tailWord_2386955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2386955).length < 2 ^ (prefixWord ++ tailWord_2386955).sum := by decide
  have hdescent : baseEnd_2386955 < baseStart_2386955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2386955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387004 : List Nat := [2, 2, 2, 2, 2, 4, 1, 1, 2, 4]
def baseStart_2387004 : Nat := 118140960795 + 2387004 * 2 ^ 59
def prefixEnd_2387004 : Nat := 4983230072969 + 3 ^ 40 * 2387004 * 2
def baseEnd_2387004 : Nat := 817120250803256046381583

theorem tailTrace_2387004 : CollatzResearch.WordTrace tailWord_2387004 prefixEnd_2387004 817120250803256046381583 := by
  unfold tailWord_2387004
  simp only [CollatzResearch.WordTrace]
  refine ⟨43530594122149825336108033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58040792162866433781477377 43530594122149825336108033)
  ·
    refine ⟨32647945591612369002081025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43530594122149825336108033 32647945591612369002081025)
    ·
      refine ⟨24485959193709276751560769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32647945591612369002081025 24485959193709276751560769)
      ·
        refine ⟨18364469395281957563670577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24485959193709276751560769 18364469395281957563670577)
        ·
          refine ⟨13773352046461468172752933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18364469395281957563670577 13773352046461468172752933)
          ·
            refine ⟨2582503508711525282391175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13773352046461468172752933 2582503508711525282391175)
            ·
              refine ⟨3873755263067287923586763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582503508711525282391175 3873755263067287923586763)
              ·
                refine ⟨5810632894600931885380145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3873755263067287923586763 5810632894600931885380145)
                ·
                  refine ⟨4357974670950698914035109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5810632894600931885380145 4357974670950698914035109)
                  ·
                    refine ⟨817120250803256046381583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4357974670950698914035109 817120250803256046381583)
                    ·
                      rfl

theorem cell22_2387004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_2387004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387004 prefixEnd_2387004 := by exact prefixLift 2387004
  have htrace : WordTrace (prefixWord ++ tailWord_2387004) baseStart_2387004 baseEnd_2387004 := by
    simpa [prefixWord, tailWord_2387004, baseEnd_2387004] using wordTrace_append hprefix tailTrace_2387004
  have hstable : (prefixWord ++ tailWord_2387004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387004).length < 2 ^ (prefixWord ++ tailWord_2387004).sum := by decide
  have hdescent : baseEnd_2387004 < baseStart_2387004 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387111 : List Nat := [1, 1, 6, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2387111 : Nat := 118140960795 + 2387111 * 2 ^ 59
def prefixEnd_2387111 : Nat := 4983230072969 + 3 ^ 40 * 2387111 * 2
def baseEnd_2387111 : Nat := 817156879089943433956255

theorem tailTrace_2387111 : CollatzResearch.WordTrace tailWord_2387111 prefixEnd_2387111 817156879089943433956255 := by
  unfold tailWord_2387111
  simp only [CollatzResearch.WordTrace]
  refine ⟨87065090854912007946361187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58043393903274671964240791 87065090854912007946361187)
  ·
    refine ⟨130597636282368011919541781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87065090854912007946361187 130597636282368011919541781)
    ·
      refine ⟨6121764200736000558728521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 130597636282368011919541781 6121764200736000558728521)
      ·
        refine ⟨4591323150552000419046391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6121764200736000558728521 4591323150552000419046391)
        ·
          refine ⟨6886984725828000628569587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4591323150552000419046391 6886984725828000628569587)
          ·
            refine ⟨10330477088742000942854381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6886984725828000628569587 10330477088742000942854381)
            ·
              refine ⟨3873928908278250353570393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10330477088742000942854381 3873928908278250353570393)
              ·
                refine ⟨2905446681208687765177795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3873928908278250353570393 2905446681208687765177795)
                ·
                  refine ⟨4358170021813031647766693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2905446681208687765177795 4358170021813031647766693)
                  ·
                    refine ⟨817156879089943433956255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4358170021813031647766693 817156879089943433956255)
                    ·
                      rfl

theorem cell22_2387111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2387111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387111 prefixEnd_2387111 := by exact prefixLift 2387111
  have htrace : WordTrace (prefixWord ++ tailWord_2387111) baseStart_2387111 baseEnd_2387111 := by
    simpa [prefixWord, tailWord_2387111, baseEnd_2387111] using wordTrace_append hprefix tailTrace_2387111
  have hstable : (prefixWord ++ tailWord_2387111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387111).length < 2 ^ (prefixWord ++ tailWord_2387111).sum := by decide
  have hdescent : baseEnd_2387111 < baseStart_2387111 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387158 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 1, 5]
def baseStart_2387158 : Nat := 118140960795 + 2387158 * 2 ^ 59
def prefixEnd_2387158 : Nat := 4983230072969 + 3 ^ 40 * 2387158 * 2
def baseEnd_2387158 : Nat := 817172968150450978031111

theorem tailTrace_2387158 : CollatzResearch.WordTrace tailWord_2387158 prefixEnd_2387158 817172968150450978031111 := by
  unfold tailWord_2387158
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441675317858858435832633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58044536723827823315548085 5441675317858858435832633)
  ·
    refine ⟨4081256488394143826874475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5441675317858858435832633 4081256488394143826874475)
    ·
      refine ⟨6121884732591215740311713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4081256488394143826874475 6121884732591215740311713)
      ·
        refine ⟨4591413549443411805233785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6121884732591215740311713 4591413549443411805233785)
        ·
          refine ⟨3443560162082558853925339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4591413549443411805233785 3443560162082558853925339)
          ·
            refine ⟨5165340243123838280888009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443560162082558853925339 5165340243123838280888009)
            ·
              refine ⟨3874005182342878710666007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5165340243123838280888009 3874005182342878710666007)
              ·
                refine ⟨5811007773514318065999011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3874005182342878710666007 5811007773514318065999011)
                ·
                  refine ⟨8716511660271477098998517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5811007773514318065999011 8716511660271477098998517)
                  ·
                    refine ⟨817172968150450978031111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8716511660271477098998517 817172968150450978031111)
                    ·
                      rfl

theorem cell22_2387158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 1, 5].length) (baseStart_2387158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387158 prefixEnd_2387158 := by exact prefixLift 2387158
  have htrace : WordTrace (prefixWord ++ tailWord_2387158) baseStart_2387158 baseEnd_2387158 := by
    simpa [prefixWord, tailWord_2387158, baseEnd_2387158] using wordTrace_append hprefix tailTrace_2387158
  have hstable : (prefixWord ++ tailWord_2387158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387158).length < 2 ^ (prefixWord ++ tailWord_2387158).sum := by decide
  have hdescent : baseEnd_2387158 < baseStart_2387158 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387169 : List Nat := [1, 2, 3, 1, 3, 2, 1, 1, 5, 3]
def baseStart_2387169 : Nat := 118140960795 + 2387169 * 2 ^ 59
def prefixEnd_2387169 : Nat := 4983230072969 + 3 ^ 40 * 2387169 * 2
def baseEnd_2387169 : Nat := 817176733675250616006077

theorem tailTrace_2387169 : CollatzResearch.WordTrace tailWord_2387169 prefixEnd_2387169 817176733675250616006077 := by
  unfold tailWord_2387169
  simp only [CollatzResearch.WordTrace]
  refine ⟨87067206288701883851972561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58044804192467922567981707 87067206288701883851972561)
  ·
    refine ⟨65300404716526412888979421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87067206288701883851972561 65300404716526412888979421)
    ·
      refine ⟨24487651768697404833367283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65300404716526412888979421 24487651768697404833367283)
      ·
        refine ⟨36731477653046107250050925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24487651768697404833367283 36731477653046107250050925)
        ·
          refine ⟨13774304119892290218769097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36731477653046107250050925 13774304119892290218769097)
          ·
            refine ⟨10330728089919217664076823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13774304119892290218769097 10330728089919217664076823)
            ·
              refine ⟨15496092134878826496115235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10330728089919217664076823 15496092134878826496115235)
              ·
                refine ⟨23244138202318239744172853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15496092134878826496115235 23244138202318239744172853)
                ·
                  refine ⟨2179137956467334976016205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 23244138202318239744172853 2179137956467334976016205)
                  ·
                    refine ⟨817176733675250616006077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2179137956467334976016205 817176733675250616006077)
                    ·
                      rfl

theorem cell22_2387169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 1, 1, 5, 3].length) (baseStart_2387169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387169 prefixEnd_2387169 := by exact prefixLift 2387169
  have htrace : WordTrace (prefixWord ++ tailWord_2387169) baseStart_2387169 baseEnd_2387169 := by
    simpa [prefixWord, tailWord_2387169, baseEnd_2387169] using wordTrace_append hprefix tailTrace_2387169
  have hstable : (prefixWord ++ tailWord_2387169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387169).length < 2 ^ (prefixWord ++ tailWord_2387169).sum := by decide
  have hdescent : baseEnd_2387169 < baseStart_2387169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387173 : List Nat := [1, 3, 1, 4, 4, 1, 1, 1, 2, 4]
def baseStart_2387173 : Nat := 118140960795 + 2387173 * 2 ^ 59
def prefixEnd_2387173 : Nat := 4983230072969 + 3 ^ 40 * 2387173 * 2
def baseEnd_2387173 : Nat := 817178102956995938906065

theorem tailTrace_2387173 : CollatzResearch.WordTrace tailWord_2387173 prefixEnd_2387173 817178102956995938906065 := by
  unfold tailWord_2387173
  simp only [CollatzResearch.WordTrace]
  refine ⟨87067352180687392535118173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58044901453791595023412115 87067352180687392535118173)
  ·
    refine ⟨32650257067757772200669315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87067352180687392535118173 32650257067757772200669315)
    ·
      refine ⟨48975385601636658301003973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32650257067757772200669315 48975385601636658301003973)
      ·
        refine ⟨9182884800306873431438245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48975385601636658301003973 9182884800306873431438245)
        ·
          refine ⟨1721790900057538768394671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9182884800306873431438245 1721790900057538768394671)
          ·
            refine ⟨2582686350086308152592007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1721790900057538768394671 2582686350086308152592007)
            ·
              refine ⟨3874029525129462228888011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2582686350086308152592007 3874029525129462228888011)
              ·
                refine ⟨5811044287694193343332017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3874029525129462228888011 5811044287694193343332017)
                ·
                  refine ⟨4358283215770645007499013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5811044287694193343332017 4358283215770645007499013)
                  ·
                    refine ⟨817178102956995938906065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4358283215770645007499013 817178102956995938906065)
                    ·
                      rfl

theorem cell22_2387173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 1, 2, 4].length) (baseStart_2387173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387173 prefixEnd_2387173 := by exact prefixLift 2387173
  have htrace : WordTrace (prefixWord ++ tailWord_2387173) baseStart_2387173 baseEnd_2387173 := by
    simpa [prefixWord, tailWord_2387173, baseEnd_2387173] using wordTrace_append hprefix tailTrace_2387173
  have hstable : (prefixWord ++ tailWord_2387173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387173).length < 2 ^ (prefixWord ++ tailWord_2387173).sum := by decide
  have hdescent : baseEnd_2387173 < baseStart_2387173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387188 : List Nat := [2, 6, 1, 2, 1, 1, 9]
def baseStart_2387188 : Nat := 118140960795 + 2387188 * 2 ^ 59
def prefixEnd_2387188 : Nat := 4983230072969 + 3 ^ 40 * 2387188 * 2
def baseEnd_2387188 : Nat := 30266045843094107399297

theorem tailTrace_2387188 : CollatzResearch.WordTrace tailWord_2387188 prefixEnd_2387188 30266045843094107399297 := by
  unfold tailWord_2387188
  simp only [CollatzResearch.WordTrace]
  refine ⟨43533949637816525048457109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58045266183755366731276145 43533949637816525048457109)
  ·
    refine ⟨2040653889272649611646427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 43533949637816525048457109 2040653889272649611646427)
    ·
      refine ⟨3060980833908974417469641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2040653889272649611646427 3060980833908974417469641)
      ·
        refine ⟨2295735625431730813102231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3060980833908974417469641 2295735625431730813102231)
        ·
          refine ⟨3443603438147596219653347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295735625431730813102231 3443603438147596219653347)
          ·
            refine ⟨5165405157221394329480021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443603438147596219653347 5165405157221394329480021)
            ·
              refine ⟨30266045843094107399297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5165405157221394329480021 30266045843094107399297)
              ·
                rfl

theorem cell22_2387188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 9].length) (baseStart_2387188 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387188 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387188 prefixEnd_2387188 := by exact prefixLift 2387188
  have htrace : WordTrace (prefixWord ++ tailWord_2387188) baseStart_2387188 baseEnd_2387188 := by
    simpa [prefixWord, tailWord_2387188, baseEnd_2387188] using wordTrace_append hprefix tailTrace_2387188
  have hstable : (prefixWord ++ tailWord_2387188).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387188).length < 2 ^ (prefixWord ++ tailWord_2387188).sum := by decide
  have hdescent : baseEnd_2387188 < baseStart_2387188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387199 : List Nat := [1, 1, 2, 2, 1, 5, 3, 2, 5]
def baseStart_2387199 : Nat := 118140960795 + 2387199 * 2 ^ 59
def prefixEnd_2387199 : Nat := 4983230072969 + 3 ^ 40 * 2387199 * 2
def baseEnd_2387199 : Nat := 272395667762780179251995

theorem tailTrace_2387199 : CollatzResearch.WordTrace tailWord_2387199 prefixEnd_2387199 272395667762780179251995 := by
  unfold tailWord_2387199
  simp only [CollatzResearch.WordTrace]
  refine ⟨87068300478593198975564651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58045533652395465983709767 87068300478593198975564651)
  ·
    refine ⟨130602450717889798463346977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87068300478593198975564651 130602450717889798463346977)
    ·
      refine ⟨97951838038417348847510233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130602450717889798463346977 97951838038417348847510233)
      ·
        refine ⟨73463878528813011635632675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 97951838038417348847510233 73463878528813011635632675)
        ·
          refine ⟨110195817793219517453449013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73463878528813011635632675 110195817793219517453449013)
          ·
            refine ⟨10330857918114329761260845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110195817793219517453449013 10330857918114329761260845)
            ·
              refine ⟨3874071719292873660472817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10330857918114329761260845 3874071719292873660472817)
              ·
                refine ⟨2905553789469655245354613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3874071719292873660472817 2905553789469655245354613)
                ·
                  refine ⟨272395667762780179251995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2905553789469655245354613 272395667762780179251995)
                  ·
                    rfl

theorem cell22_2387199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 2, 5].length) (baseStart_2387199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387199 prefixEnd_2387199 := by exact prefixLift 2387199
  have htrace : WordTrace (prefixWord ++ tailWord_2387199) baseStart_2387199 baseEnd_2387199 := by
    simpa [prefixWord, tailWord_2387199, baseEnd_2387199] using wordTrace_append hprefix tailTrace_2387199
  have hstable : (prefixWord ++ tailWord_2387199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387199).length < 2 ^ (prefixWord ++ tailWord_2387199).sum := by decide
  have hdescent : baseEnd_2387199 < baseStart_2387199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387214 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 2, 5]
def baseStart_2387214 : Nat := 118140960795 + 2387214 * 2 ^ 59
def prefixEnd_2387214 : Nat := 4983230072969 + 3 ^ 40 * 2387214 * 2
def baseEnd_2387214 : Nat := 817192138094885498630939

theorem tailTrace_2387214 : CollatzResearch.WordTrace tailWord_2387214 prefixEnd_2387214 817192138094885498630939 := by
  unfold tailWord_2387214
  simp only [CollatzResearch.WordTrace]
  refine ⟨10883605946692357067170087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58045898382359237691573797 10883605946692357067170087)
  ·
    refine ⟨16325408920038535600755131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10883605946692357067170087 16325408920038535600755131)
    ·
      refine ⟨24488113380057803401132697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16325408920038535600755131 24488113380057803401132697)
      ·
        refine ⟨18366085035043352550849523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24488113380057803401132697 18366085035043352550849523)
        ·
          refine ⟨27549127552565028826274285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18366085035043352550849523 27549127552565028826274285)
          ·
            refine ⟨10330922832211885809852857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27549127552565028826274285 10330922832211885809852857)
            ·
              refine ⟨7748192124158914357389643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10330922832211885809852857 7748192124158914357389643)
              ·
                refine ⟨11622288186238371536084465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7748192124158914357389643 11622288186238371536084465)
                ·
                  refine ⟨8716716139678778652063349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11622288186238371536084465 8716716139678778652063349)
                  ·
                    refine ⟨817192138094885498630939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8716716139678778652063349 817192138094885498630939)
                    ·
                      rfl

theorem cell22_2387214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 2, 5].length) (baseStart_2387214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387214 prefixEnd_2387214 := by exact prefixLift 2387214
  have htrace : WordTrace (prefixWord ++ tailWord_2387214) baseStart_2387214 baseEnd_2387214 := by
    simpa [prefixWord, tailWord_2387214, baseEnd_2387214] using wordTrace_append hprefix tailTrace_2387214
  have hstable : (prefixWord ++ tailWord_2387214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387214).length < 2 ^ (prefixWord ++ tailWord_2387214).sum := by decide
  have hdescent : baseEnd_2387214 < baseStart_2387214 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387254 : List Nat := [5, 1, 2, 3, 1, 1, 3, 2, 1, 3]
def baseStart_2387254 : Nat := 118140960795 + 2387254 * 2 ^ 59
def prefixEnd_2387254 : Nat := 4983230072969 + 3 ^ 40 * 2387254 * 2
def baseEnd_2387254 : Nat := 817205830912338727630817

theorem tailTrace_2387254 : CollatzResearch.WordTrace tailWord_2387254 prefixEnd_2387254 817205830912338727630817 := by
  unfold tailWord_2387254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5441894155837121460551051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58046870995595962245877877 5441894155837121460551051)
  ·
    refine ⟨8162841233755682190826577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5441894155837121460551051 8162841233755682190826577)
    ·
      refine ⟨6122130925316761643119933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8162841233755682190826577 6122130925316761643119933)
      ·
        refine ⟨2295799096993785616169975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6122130925316761643119933 2295799096993785616169975)
        ·
          refine ⟨3443698645490678424254963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2295799096993785616169975 3443698645490678424254963)
          ·
            refine ⟨5165547968236017636382445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443698645490678424254963 5165547968236017636382445)
            ·
              refine ⟨1937080488088506613643417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5165547968236017636382445 1937080488088506613643417)
              ·
                refine ⟨1452810366066379960232563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1937080488088506613643417 1452810366066379960232563)
                ·
                  refine ⟨2179215549099569940348845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1452810366066379960232563 2179215549099569940348845)
                  ·
                    refine ⟨817205830912338727630817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2179215549099569940348845 817205830912338727630817)
                    ·
                      rfl

theorem cell22_2387254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_2387254 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387254 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387254 prefixEnd_2387254 := by exact prefixLift 2387254
  have htrace : WordTrace (prefixWord ++ tailWord_2387254) baseStart_2387254 baseEnd_2387254 := by
    simpa [prefixWord, tailWord_2387254, baseEnd_2387254] using wordTrace_append hprefix tailTrace_2387254
  have hstable : (prefixWord ++ tailWord_2387254).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387254).length < 2 ^ (prefixWord ++ tailWord_2387254).sum := by decide
  have hdescent : baseEnd_2387254 < baseStart_2387254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387306 : List Nat := [3, 1, 3, 3, 3, 9]
def baseStart_2387306 : Nat := 118140960795 + 2387306 * 2 ^ 59
def prefixEnd_2387306 : Nat := 4983230072969 + 3 ^ 40 * 2387306 * 2
def baseEnd_2387306 : Nat := 10089180636728739818897

theorem tailTrace_2387306 : CollatzResearch.WordTrace tailWord_2387306 prefixEnd_2387306 10089180636728739818897 := by
  unfold tailWord_2387306
  simp only [CollatzResearch.WordTrace]
  refine ⟨21768050772301389062427443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58048135392803704166473181 21768050772301389062427443)
  ·
    refine ⟨32652076158452083593641165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21768050772301389062427443 32652076158452083593641165)
    ·
      refine ⟨12244528559419531347615437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32652076158452083593641165 12244528559419531347615437)
      ·
        refine ⟨4591698209782324255355789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12244528559419531347615437 4591698209782324255355789)
        ·
          refine ⟨1721886828668371595758421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4591698209782324255355789 1721886828668371595758421)
          ·
            refine ⟨10089180636728739818897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 1721886828668371595758421 10089180636728739818897)
            ·
              rfl

theorem cell22_2387306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 9].length) (baseStart_2387306 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387306 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387306 prefixEnd_2387306 := by exact prefixLift 2387306
  have htrace : WordTrace (prefixWord ++ tailWord_2387306) baseStart_2387306 baseEnd_2387306 := by
    simpa [prefixWord, tailWord_2387306, baseEnd_2387306] using wordTrace_append hprefix tailTrace_2387306
  have hstable : (prefixWord ++ tailWord_2387306).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387306).length < 2 ^ (prefixWord ++ tailWord_2387306).sum := by decide
  have hdescent : baseEnd_2387306 < baseStart_2387306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387368 : List Nat := [2, 1, 6, 1, 2, 1, 1, 1, 7]
def baseStart_2387368 : Nat := 118140960795 + 2387368 * 2 ^ 59
def prefixEnd_2387368 : Nat := 4983230072969 + 3 ^ 40 * 2387368 * 2
def baseEnd_2387368 : Nat := 272414951814026810093489

theorem tailTrace_2387368 : CollatzResearch.WordTrace tailWord_2387368 prefixEnd_2387368 272414951814026810093489 := by
  unfold tailWord_2387368
  simp only [CollatzResearch.WordTrace]
  refine ⟨43537232207490470419233379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58049642943320627225644505 43537232207490470419233379)
  ·
    refine ⟨65305848311235705628850069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43537232207490470419233379 65305848311235705628850069)
    ·
      refine ⟨3061211639589173701352347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 65305848311235705628850069 3061211639589173701352347)
      ·
        refine ⟨4591817459383760552028521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3061211639589173701352347 4591817459383760552028521)
        ·
          refine ⟨3443863094537820414021391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4591817459383760552028521 3443863094537820414021391)
          ·
            refine ⟨5165794641806730621032087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443863094537820414021391 5165794641806730621032087)
            ·
              refine ⟨7748691962710095931548131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5165794641806730621032087 7748691962710095931548131)
              ·
                refine ⟨11623037944065143897322197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7748691962710095931548131 11623037944065143897322197)
                ·
                  refine ⟨272414951814026810093489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11623037944065143897322197 272414951814026810093489)
                  ·
                    rfl

theorem cell22_2387368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 1, 7].length) (baseStart_2387368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387368 prefixEnd_2387368 := by exact prefixLift 2387368
  have htrace : WordTrace (prefixWord ++ tailWord_2387368) baseStart_2387368 baseEnd_2387368 := by
    simpa [prefixWord, tailWord_2387368, baseEnd_2387368] using wordTrace_append hprefix tailTrace_2387368
  have hstable : (prefixWord ++ tailWord_2387368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387368).length < 2 ^ (prefixWord ++ tailWord_2387368).sum := by decide
  have hdescent : baseEnd_2387368 < baseStart_2387368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387441 : List Nat := [1, 2, 2, 2, 3, 3, 2, 7]
def baseStart_2387441 : Nat := 118140960795 + 2387441 * 2 ^ 59
def prefixEnd_2387441 : Nat := 4983230072969 + 3 ^ 40 * 2387441 * 2
def baseEnd_2387441 : Nat := 90807760537103619245027

theorem tailTrace_2387441 : CollatzResearch.WordTrace tailWord_2387441 prefixEnd_2387441 90807760537103619245027 := by
  unfold tailWord_2387441
  simp only [CollatzResearch.WordTrace]
  refine ⟨87077126943716474305874177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58051417962477649537249451 87077126943716474305874177)
  ·
    refine ⟨65307845207787355729405633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87077126943716474305874177 65307845207787355729405633)
    ·
      refine ⟨48980883905840516797054225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65307845207787355729405633 48980883905840516797054225)
      ·
        refine ⟨36735662929380387597790669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48980883905840516797054225 36735662929380387597790669)
        ·
          refine ⟨13775873598517645349171501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36735662929380387597790669 13775873598517645349171501)
          ·
            refine ⟨5165952599444117005939313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13775873598517645349171501 5165952599444117005939313)
            ·
              refine ⟨3874464449583087754454485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5165952599444117005939313 3874464449583087754454485)
              ·
                refine ⟨90807760537103619245027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3874464449583087754454485 90807760537103619245027)
                ·
                  rfl

theorem cell22_2387441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 7].length) (baseStart_2387441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387441 prefixEnd_2387441 := by exact prefixLift 2387441
  have htrace : WordTrace (prefixWord ++ tailWord_2387441) baseStart_2387441 baseEnd_2387441 := by
    simpa [prefixWord, tailWord_2387441, baseEnd_2387441] using wordTrace_append hprefix tailTrace_2387441
  have hstable : (prefixWord ++ tailWord_2387441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387441).length < 2 ^ (prefixWord ++ tailWord_2387441).sum := by decide
  have hdescent : baseEnd_2387441 < baseStart_2387441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387458 : List Nat := [3, 4, 1, 2, 1, 1, 2, 8]
def baseStart_2387458 : Nat := 118140960795 + 2387458 * 2 ^ 59
def prefixEnd_2387458 : Nat := 4983230072969 + 3 ^ 40 * 2387458 * 2
def baseEnd_2387458 : Nat := 90808407142372243947799

theorem tailTrace_2387458 : CollatzResearch.WordTrace tailWord_2387458 prefixEnd_2387458 90808407142372243947799 := by
  unfold tailWord_2387458
  simp only [CollatzResearch.WordTrace]
  refine ⟨21769436746163721552310757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58051831323103257472828685 21769436746163721552310757)
  ·
    refine ⟨4081769389905697791058267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 21769436746163721552310757 4081769389905697791058267)
    ·
      refine ⟨6122654084858546686587401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4081769389905697791058267 6122654084858546686587401)
      ·
        refine ⟨4591990563643910014940551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6122654084858546686587401 4591990563643910014940551)
        ·
          refine ⟨6887985845465865022410827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4591990563643910014940551 6887985845465865022410827)
          ·
            refine ⟨10331978768198797533616241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6887985845465865022410827 10331978768198797533616241)
            ·
              refine ⟨7748984076149098150212181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10331978768198797533616241 7748984076149098150212181)
              ·
                refine ⟨90808407142372243947799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7748984076149098150212181 90808407142372243947799)
                ·
                  rfl

theorem cell22_2387458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 8].length) (baseStart_2387458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387458 prefixEnd_2387458 := by exact prefixLift 2387458
  have htrace : WordTrace (prefixWord ++ tailWord_2387458) baseStart_2387458 baseEnd_2387458 := by
    simpa [prefixWord, tailWord_2387458, baseEnd_2387458] using wordTrace_append hprefix tailTrace_2387458
  have hstable : (prefixWord ++ tailWord_2387458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387458).length < 2 ^ (prefixWord ++ tailWord_2387458).sum := by decide
  have hdescent : baseEnd_2387458 < baseStart_2387458 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387460 : List Nat := [2, 3, 2, 3, 2, 1, 2, 1, 2, 4]
def baseStart_2387460 : Nat := 118140960795 + 2387460 * 2 ^ 59
def prefixEnd_2387460 : Nat := 4983230072969 + 3 ^ 40 * 2387460 * 2
def baseEnd_2387460 : Nat := 817276348922222856980185

theorem tailTrace_2387460 : CollatzResearch.WordTrace tailWord_2387460 prefixEnd_2387460 817276348922222856980185 := by
  unfold tailWord_2387460
  simp only [CollatzResearch.WordTrace]
  refine ⟨43538909965323820275407917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58051879953765093700543889 43538909965323820275407917)
  ·
    refine ⟨16327091236996432603277969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43538909965323820275407917 16327091236996432603277969)
    ·
      refine ⟨12245318427747324452458477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16327091236996432603277969 12245318427747324452458477)
      ·
        refine ⟨4591994410405246669671929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12245318427747324452458477 4591994410405246669671929)
        ·
          refine ⟨3443995807803935002253947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4591994410405246669671929 3443995807803935002253947)
          ·
            refine ⟨5165993711705902503380921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3443995807803935002253947 5165993711705902503380921)
            ·
              refine ⟨3874495283779426877535691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5165993711705902503380921 3874495283779426877535691)
              ·
                refine ⟨5811742925669140316303537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3874495283779426877535691 5811742925669140316303537)
                ·
                  refine ⟨4358807194251855237227653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5811742925669140316303537 4358807194251855237227653)
                  ·
                    refine ⟨817276348922222856980185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4358807194251855237227653 817276348922222856980185)
                    ·
                      rfl

theorem cell22_2387460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 1, 2, 4].length) (baseStart_2387460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387460 prefixEnd_2387460 := by exact prefixLift 2387460
  have htrace : WordTrace (prefixWord ++ tailWord_2387460) baseStart_2387460 baseEnd_2387460 := by
    simpa [prefixWord, tailWord_2387460, baseEnd_2387460] using wordTrace_append hprefix tailTrace_2387460
  have hstable : (prefixWord ++ tailWord_2387460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387460).length < 2 ^ (prefixWord ++ tailWord_2387460).sum := by decide
  have hdescent : baseEnd_2387460 < baseStart_2387460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387546 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_2387546 : Nat := 118140960795 + 2387546 * 2 ^ 59
def prefixEnd_2387546 : Nat := 4983230072969 + 3 ^ 40 * 2387546 * 2
def baseEnd_2387546 : Nat := 817305788479747299329921

theorem tailTrace_2387546 : CollatzResearch.WordTrace tailWord_2387546 prefixEnd_2387546 817305788479747299329921 := by
  unfold tailWord_2387546
  simp only [CollatzResearch.WordTrace]
  refine ⟨21770239152084019309611623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58053971072224051492297661 21770239152084019309611623)
  ·
    refine ⟨32655358728126028964417435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21770239152084019309611623 32655358728126028964417435)
    ·
      refine ⟨48983038092189043446626153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32655358728126028964417435 48983038092189043446626153)
      ·
        refine ⟨36737278569141782584969615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48983038092189043446626153 36737278569141782584969615)
        ·
          refine ⟨55105917853712673877454423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36737278569141782584969615 55105917853712673877454423)
          ·
            refine ⟨82658876780569010816181635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55105917853712673877454423 82658876780569010816181635)
            ·
              refine ⟨123988315170853516224272453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82658876780569010816181635 123988315170853516224272453)
              ·
                refine ⟨23247809094535034292051085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 123988315170853516224272453 23247809094535034292051085)
                ·
                  refine ⟨8717928410450637859519157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23247809094535034292051085 8717928410450637859519157)
                  ·
                    refine ⟨817305788479747299329921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8717928410450637859519157 817305788479747299329921)
                    ·
                      rfl

theorem cell22_2387546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_2387546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387546 prefixEnd_2387546 := by exact prefixLift 2387546
  have htrace : WordTrace (prefixWord ++ tailWord_2387546) baseStart_2387546 baseEnd_2387546 := by
    simpa [prefixWord, tailWord_2387546, baseEnd_2387546] using wordTrace_append hprefix tailTrace_2387546
  have hstable : (prefixWord ++ tailWord_2387546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387546).length < 2 ^ (prefixWord ++ tailWord_2387546).sum := by decide
  have hdescent : baseEnd_2387546 < baseStart_2387546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387548 : List Nat := [2, 2, 4, 1, 2, 1, 1, 3, 6]
def baseStart_2387548 : Nat := 118140960795 + 2387548 * 2 ^ 59
def prefixEnd_2387548 : Nat := 4983230072969 + 3 ^ 40 * 2387548 * 2
def baseEnd_2387548 : Nat := 272435491040206653593305

theorem tailTrace_2387548 : CollatzResearch.WordTrace tailWord_2387548 prefixEnd_2387548 272435491040206653593305 := by
  unfold tailWord_2387548
  simp only [CollatzResearch.WordTrace]
  refine ⟨43540514777164415790009649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58054019702885887720012865 43540514777164415790009649)
  ·
    refine ⟨32655386082873311842507237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43540514777164415790009649 32655386082873311842507237)
    ·
      refine ⟨6122884890538745970470107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 32655386082873311842507237 6122884890538745970470107)
      ·
        refine ⟨9184327335808118955705161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6122884890538745970470107 9184327335808118955705161)
        ·
          refine ⟨6888245501856089216778871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9184327335808118955705161 6888245501856089216778871)
          ·
            refine ⟨10332368252784133825168307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6888245501856089216778871 10332368252784133825168307)
            ·
              refine ⟨15498552379176200737752461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10332368252784133825168307 15498552379176200737752461)
              ·
                refine ⟨5811957142191075276657173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15498552379176200737752461 5811957142191075276657173)
                ·
                  refine ⟨272435491040206653593305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5811957142191075276657173 272435491040206653593305)
                  ·
                    rfl

theorem cell22_2387548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_2387548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387548 prefixEnd_2387548 := by exact prefixLift 2387548
  have htrace : WordTrace (prefixWord ++ tailWord_2387548) baseStart_2387548 baseEnd_2387548 := by
    simpa [prefixWord, tailWord_2387548, baseEnd_2387548] using wordTrace_append hprefix tailTrace_2387548
  have hstable : (prefixWord ++ tailWord_2387548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387548).length < 2 ^ (prefixWord ++ tailWord_2387548).sum := by decide
  have hdescent : baseEnd_2387548 < baseStart_2387548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387561 : List Nat := [1, 2, 1, 1, 1, 4, 3, 2, 1, 6]
def baseStart_2387561 : Nat := 118140960795 + 2387561 * 2 ^ 59
def prefixEnd_2387561 : Nat := 4983230072969 + 3 ^ 40 * 2387561 * 2
def baseEnd_2387561 : Nat := 817310923286292260204875

theorem tailTrace_2387561 : CollatzResearch.WordTrace tailWord_2387561 prefixEnd_2387561 817310923286292260204875 := by
  unfold tailWord_2387561
  simp only [CollatzResearch.WordTrace]
  refine ⟨87081503703281734800242537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58054335802187823200161691 87081503703281734800242537)
  ·
    refine ⟨65311127777461301100181903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87081503703281734800242537 65311127777461301100181903)
    ·
      refine ⟨97966691666191951650272855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65311127777461301100181903 97966691666191951650272855)
      ·
        refine ⟨146950037499287927475409283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97966691666191951650272855 146950037499287927475409283)
        ·
          refine ⟨220425056248931891213113925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 146950037499287927475409283 220425056248931891213113925)
          ·
            refine ⟨41329698046674729602458861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220425056248931891213113925 41329698046674729602458861)
            ·
              refine ⟨15498636767503023600922073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 41329698046674729602458861 15498636767503023600922073)
              ·
                refine ⟨11623977575627267700691555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15498636767503023600922073 11623977575627267700691555)
                ·
                  refine ⟨17435966363440901551037333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11623977575627267700691555 17435966363440901551037333)
                  ·
                    refine ⟨817310923286292260204875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17435966363440901551037333 817310923286292260204875)
                    ·
                      rfl

theorem cell22_2387561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 6].length) (baseStart_2387561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387561 prefixEnd_2387561 := by exact prefixLift 2387561
  have htrace : WordTrace (prefixWord ++ tailWord_2387561) baseStart_2387561 baseEnd_2387561 := by
    simpa [prefixWord, tailWord_2387561, baseEnd_2387561] using wordTrace_append hprefix tailTrace_2387561
  have hstable : (prefixWord ++ tailWord_2387561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387561).length < 2 ^ (prefixWord ++ tailWord_2387561).sum := by decide
  have hdescent : baseEnd_2387561 < baseStart_2387561 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387614 : List Nat := [4, 3, 1, 1, 1, 2, 4, 1, 2, 3]
def baseStart_2387614 : Nat := 118140960795 + 2387614 * 2 ^ 59
def prefixEnd_2387614 : Nat := 4983230072969 + 3 ^ 40 * 2387614 * 2
def baseEnd_2387614 : Nat := 817329066269417788629713

theorem tailTrace_2387614 : CollatzResearch.WordTrace tailWord_2387614 prefixEnd_2387614 817329066269417788629713 := by
  unfold tailWord_2387614
  simp only [CollatzResearch.WordTrace]
  refine ⟨10885429596511215606490237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 58055624514726483234614597 10885429596511215606490237)
  ·
    refine ⟨4082036098691705852433839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10885429596511215606490237 4082036098691705852433839)
    ·
      refine ⟨6123054148037558778650759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4082036098691705852433839 6123054148037558778650759)
      ·
        refine ⟨9184581222056338167976139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6123054148037558778650759 9184581222056338167976139)
        ·
          refine ⟨13776871833084507251964209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9184581222056338167976139 13776871833084507251964209)
          ·
            refine ⟨10332653874813380438973157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13776871833084507251964209 10332653874813380438973157)
            ·
              refine ⟨1937372601527508832307467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10332653874813380438973157 1937372601527508832307467)
              ·
                refine ⟨2906058902291263248461201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937372601527508832307467 2906058902291263248461201)
                ·
                  refine ⟨2179544176718447436345901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2906058902291263248461201 2179544176718447436345901)
                  ·
                    refine ⟨817329066269417788629713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2179544176718447436345901 817329066269417788629713)
                    ·
                      rfl

theorem cell22_2387614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 1, 2, 3].length) (baseStart_2387614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387614 prefixEnd_2387614 := by exact prefixLift 2387614
  have htrace : WordTrace (prefixWord ++ tailWord_2387614) baseStart_2387614 baseEnd_2387614 := by
    simpa [prefixWord, tailWord_2387614, baseEnd_2387614] using wordTrace_append hprefix tailTrace_2387614
  have hstable : (prefixWord ++ tailWord_2387614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387614).length < 2 ^ (prefixWord ++ tailWord_2387614).sum := by decide
  have hdescent : baseEnd_2387614 < baseStart_2387614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387650 : List Nat := [3, 5, 1, 2, 2, 1, 2, 2, 4]
def baseStart_2387650 : Nat := 118140960795 + 2387650 * 2 ^ 59
def prefixEnd_2387650 : Nat := 4983230072969 + 3 ^ 40 * 2387650 * 2
def baseEnd_2387650 : Nat := 272447129935041898243201

theorem tailTrace_2387650 : CollatzResearch.WordTrace tailWord_2387650 prefixEnd_2387650 272447129935041898243201 := by
  unfold tailWord_2387650
  simp only [CollatzResearch.WordTrace]
  refine ⟨21771187449989825750058101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58056499866639535333488269 21771187449989825750058101)
  ·
    refine ⟨2041048823436546164067947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 21771187449989825750058101 2041048823436546164067947)
    ·
      refine ⟨3061573235154819246101921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2041048823436546164067947 3061573235154819246101921)
      ·
        refine ⟨2296179926366114434576441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3061573235154819246101921 2296179926366114434576441)
        ·
          refine ⟨1722134944774585825932331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2296179926366114434576441 1722134944774585825932331)
          ·
            refine ⟨2583202417161878738898497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722134944774585825932331 2583202417161878738898497)
            ·
              refine ⟨1937401812871409054173873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2583202417161878738898497 1937401812871409054173873)
              ·
                refine ⟨1453051359653556790630405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1937401812871409054173873 1453051359653556790630405)
                ·
                  refine ⟨272447129935041898243201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453051359653556790630405 272447129935041898243201)
                  ·
                    rfl

theorem cell22_2387650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_2387650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387650 prefixEnd_2387650 := by exact prefixLift 2387650
  have htrace : WordTrace (prefixWord ++ tailWord_2387650) baseStart_2387650 baseEnd_2387650 := by
    simpa [prefixWord, tailWord_2387650, baseEnd_2387650] using wordTrace_append hprefix tailTrace_2387650
  have hstable : (prefixWord ++ tailWord_2387650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387650).length < 2 ^ (prefixWord ++ tailWord_2387650).sum := by decide
  have hdescent : baseEnd_2387650 < baseStart_2387650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387685 : List Nat := [1, 3, 1, 4, 1, 1, 2, 4, 1, 4]
def baseStart_2387685 : Nat := 118140960795 + 2387685 * 2 ^ 59
def prefixEnd_2387685 : Nat := 4983230072969 + 3 ^ 40 * 2387685 * 2
def baseEnd_2387685 : Nat := 817353371020397270104495

theorem tailTrace_2387685 : CollatzResearch.WordTrace tailWord_2387685 prefixEnd_2387685 817353371020397270104495 := by
  unfold tailWord_2387685
  simp only [CollatzResearch.WordTrace]
  refine ⟨87086026354832503977756509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58057350903221669318504339 87086026354832503977756509)
  ·
    refine ⟨32657259883062188991658691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87086026354832503977756509 32657259883062188991658691)
    ·
      refine ⟨48985889824593283487488037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32657259883062188991658691 48985889824593283487488037)
      ·
        refine ⟨9184854342111240653904007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 48985889824593283487488037 9184854342111240653904007)
        ·
          refine ⟨13777281513166860980856011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9184854342111240653904007 13777281513166860980856011)
          ·
            refine ⟨20665922269750291471284017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13777281513166860980856011 20665922269750291471284017)
            ·
              refine ⟨15499441702312718603463013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20665922269750291471284017 15499441702312718603463013)
              ·
                refine ⟨2906145319183634738149315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15499441702312718603463013 2906145319183634738149315)
                ·
                  refine ⟨4359217978775452107223973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906145319183634738149315 4359217978775452107223973)
                  ·
                    refine ⟨817353371020397270104495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359217978775452107223973 817353371020397270104495)
                    ·
                      rfl

theorem cell22_2387685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 4].length) (baseStart_2387685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387685 prefixEnd_2387685 := by exact prefixLift 2387685
  have htrace : WordTrace (prefixWord ++ tailWord_2387685) baseStart_2387685 baseEnd_2387685 := by
    simpa [prefixWord, tailWord_2387685, baseEnd_2387685] using wordTrace_append hprefix tailTrace_2387685
  have hstable : (prefixWord ++ tailWord_2387685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387685).length < 2 ^ (prefixWord ++ tailWord_2387685).sum := by decide
  have hdescent : baseEnd_2387685 < baseStart_2387685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387702 : List Nat := [5, 1, 1, 1, 1, 4, 1, 3, 1, 4]
def baseStart_2387702 : Nat := 118140960795 + 2387702 * 2 ^ 59
def prefixEnd_2387702 : Nat := 4983230072969 + 3 ^ 40 * 2387702 * 2
def baseEnd_2387702 : Nat := 817359190467814892429443

theorem tailTrace_2387702 : CollatzResearch.WordTrace tailWord_2387702 prefixEnd_2387702 817359190467814892429443 := by
  unfold tailWord_2387702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5442915399735682242570335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58057764263847277254083573 5442915399735682242570335)
  ·
    refine ⟨8164373099603523363855503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5442915399735682242570335 8164373099603523363855503)
    ·
      refine ⟨12246559649405285045783255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8164373099603523363855503 12246559649405285045783255)
      ·
        refine ⟨18369839474107927568674883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12246559649405285045783255 18369839474107927568674883)
        ·
          refine ⟨27554759211161891353012325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18369839474107927568674883 27554759211161891353012325)
          ·
            refine ⟨5166517352092854628689811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 27554759211161891353012325 5166517352092854628689811)
            ·
              refine ⟨7749776028139281943034717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5166517352092854628689811 7749776028139281943034717)
              ·
                refine ⟨2906166010552230728638019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7749776028139281943034717 2906166010552230728638019)
                ·
                  refine ⟨4359249015828346092957029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906166010552230728638019 4359249015828346092957029)
                  ·
                    refine ⟨817359190467814892429443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359249015828346092957029 817359190467814892429443)
                    ·
                      rfl

theorem cell22_2387702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_2387702 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387702 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387702 prefixEnd_2387702 := by exact prefixLift 2387702
  have htrace : WordTrace (prefixWord ++ tailWord_2387702) baseStart_2387702 baseEnd_2387702 := by
    simpa [prefixWord, tailWord_2387702, baseEnd_2387702] using wordTrace_append hprefix tailTrace_2387702
  have hstable : (prefixWord ++ tailWord_2387702).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387702).length < 2 ^ (prefixWord ++ tailWord_2387702).sum := by decide
  have hdescent : baseEnd_2387702 < baseStart_2387702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387743 : List Nat := [1, 1, 2, 4, 2, 1, 1, 1, 2, 7]
def baseStart_2387743 : Nat := 118140960795 + 2387743 * 2 ^ 59
def prefixEnd_2387743 : Nat := 4983230072969 + 3 ^ 40 * 2387743 * 2
def baseEnd_2387743 : Nat := 817373225605704452154317

theorem tailTrace_2387743 : CollatzResearch.WordTrace tailWord_2387743 prefixEnd_2387743 817373225605704452154317 := by
  unfold tailWord_2387743
  simp only [CollatzResearch.WordTrace]
  refine ⟨87088141788622379883367883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58058761192414919922245255 87088141788622379883367883)
  ·
    refine ⟨130632212682933569825051825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87088141788622379883367883 130632212682933569825051825)
    ·
      refine ⟨97974159512200177368788869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130632212682933569825051825 97974159512200177368788869)
      ·
        refine ⟨18370154908537533256647913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 97974159512200177368788869 18370154908537533256647913)
        ·
          refine ⟨13777616181403149942485935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18370154908537533256647913 13777616181403149942485935)
          ·
            refine ⟨20666424272104724913728903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13777616181403149942485935 20666424272104724913728903)
            ·
              refine ⟨30999636408157087370593355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20666424272104724913728903 30999636408157087370593355)
              ·
                refine ⟨46499454612235631055890033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 30999636408157087370593355 46499454612235631055890033)
                ·
                  refine ⟨34874590959176723291917525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 46499454612235631055890033 34874590959176723291917525)
                  ·
                    refine ⟨817373225605704452154317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34874590959176723291917525 817373225605704452154317)
                    ·
                      rfl

theorem cell22_2387743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_2387743 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387743 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387743 prefixEnd_2387743 := by exact prefixLift 2387743
  have htrace : WordTrace (prefixWord ++ tailWord_2387743) baseStart_2387743 baseEnd_2387743 := by
    simpa [prefixWord, tailWord_2387743, baseEnd_2387743] using wordTrace_append hprefix tailTrace_2387743
  have hstable : (prefixWord ++ tailWord_2387743).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387743).length < 2 ^ (prefixWord ++ tailWord_2387743).sum := by decide
  have hdescent : baseEnd_2387743 < baseStart_2387743 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387745 : List Nat := [1, 2, 3, 2, 1, 3, 4, 6]
def baseStart_2387745 : Nat := 118140960795 + 2387745 * 2 ^ 59
def prefixEnd_2387745 : Nat := 4983230072969 + 3 ^ 40 * 2387745 * 2
def baseEnd_2387745 : Nat := 90819323360730790400479

theorem tailTrace_2387745 : CollatzResearch.WordTrace tailWord_2387745 prefixEnd_2387745 90819323360730790400479 := by
  unfold tailWord_2387745
  simp only [CollatzResearch.WordTrace]
  refine ⟨87088214734615134224940689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58058809823076756149960459 87088214734615134224940689)
  ·
    refine ⟨65316161050961350668705517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87088214734615134224940689 65316161050961350668705517)
    ·
      refine ⟨24493560394110506500764569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 65316161050961350668705517 24493560394110506500764569)
      ·
        refine ⟨18370170295582879875573427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24493560394110506500764569 18370170295582879875573427)
        ·
          refine ⟨27555255443374319813360141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18370170295582879875573427 27555255443374319813360141)
          ·
            refine ⟨10333220791265369930010053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27555255443374319813360141 10333220791265369930010053)
            ·
              refine ⟨1937478898362256861876885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10333220791265369930010053 1937478898362256861876885)
              ·
                refine ⟨90819323360730790400479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1937478898362256861876885 90819323360730790400479)
                ·
                  rfl

theorem cell22_2387745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 6].length) (baseStart_2387745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387745 prefixEnd_2387745 := by exact prefixLift 2387745
  have htrace : WordTrace (prefixWord ++ tailWord_2387745) baseStart_2387745 baseEnd_2387745 := by
    simpa [prefixWord, tailWord_2387745, baseEnd_2387745] using wordTrace_append hprefix tailTrace_2387745
  have hstable : (prefixWord ++ tailWord_2387745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387745).length < 2 ^ (prefixWord ++ tailWord_2387745).sum := by decide
  have hdescent : baseEnd_2387745 < baseStart_2387745 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387869 : List Nat := [1, 4, 2, 1, 2, 3, 2, 3, 4]
def baseStart_2387869 : Nat := 118140960795 + 2387869 * 2 ^ 59
def prefixEnd_2387869 : Nat := 4983230072969 + 3 ^ 40 * 2387869 * 2
def baseEnd_2387869 : Nat := 272472119326894041167977

theorem tailTrace_2387869 : CollatzResearch.WordTrace tailWord_2387869 prefixEnd_2387869 272472119326894041167977 := by
  unfold tailWord_2387869
  simp only [CollatzResearch.WordTrace]
  refine ⟨87092737386165903402454661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58061824924110602268303107 87092737386165903402454661)
  ·
    refine ⟨16329888259906106887960249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87092737386165903402454661 16329888259906106887960249)
    ·
      refine ⟨12247416194929580165970187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16329888259906106887960249 12247416194929580165970187)
      ·
        refine ⟨18371124292394370248955281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12247416194929580165970187 18371124292394370248955281)
        ·
          refine ⟨13778343219295777686716461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18371124292394370248955281 13778343219295777686716461)
          ·
            refine ⟨5166878707235916632518673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13778343219295777686716461 5166878707235916632518673)
            ·
              refine ⟨3875159030426937474389005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5166878707235916632518673 3875159030426937474389005)
              ·
                refine ⟨1453184636410101552895877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3875159030426937474389005 1453184636410101552895877)
                ·
                  refine ⟨272472119326894041167977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453184636410101552895877 272472119326894041167977)
                  ·
                    rfl

theorem cell22_2387869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 2, 3, 4].length) (baseStart_2387869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387869 prefixEnd_2387869 := by exact prefixLift 2387869
  have htrace : WordTrace (prefixWord ++ tailWord_2387869) baseStart_2387869 baseEnd_2387869 := by
    simpa [prefixWord, tailWord_2387869, baseEnd_2387869] using wordTrace_append hprefix tailTrace_2387869
  have hstable : (prefixWord ++ tailWord_2387869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387869).length < 2 ^ (prefixWord ++ tailWord_2387869).sum := by decide
  have hdescent : baseEnd_2387869 < baseStart_2387869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387871 : List Nat := [1, 1, 2, 5, 3, 2, 2, 1, 1, 4]
def baseStart_2387871 : Nat := 118140960795 + 2387871 * 2 ^ 59
def prefixEnd_2387871 : Nat := 4983230072969 + 3 ^ 40 * 2387871 * 2
def baseEnd_2387871 : Nat := 817417042621554784953925

theorem tailTrace_2387871 : CollatzResearch.WordTrace tailWord_2387871 prefixEnd_2387871 817417042621554784953925 := by
  unfold tailWord_2387871
  simp only [CollatzResearch.WordTrace]
  refine ⟨87092810332158657744027467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58061873554772438496018311 87092810332158657744027467)
  ·
    refine ⟨130639215498237986616041201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87092810332158657744027467 130639215498237986616041201)
    ·
      refine ⟨97979411623678489962030901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130639215498237986616041201 97979411623678489962030901)
      ·
        refine ⟨9185569839719858433940397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 97979411623678489962030901 9185569839719858433940397)
        ·
          refine ⟨3444588689894946912727649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9185569839719858433940397 3444588689894946912727649)
          ·
            refine ⟨2583441517421210184545737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3444588689894946912727649 2583441517421210184545737)
            ·
              refine ⟨1937581138065907638409303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2583441517421210184545737 1937581138065907638409303)
              ·
                refine ⟨2906371707098861457613955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937581138065907638409303 2906371707098861457613955)
                ·
                  refine ⟨4359557560648292186420933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2906371707098861457613955 4359557560648292186420933)
                  ·
                    refine ⟨817417042621554784953925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359557560648292186420933 817417042621554784953925)
                    ·
                      rfl

theorem cell22_2387871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 2, 2, 1, 1, 4].length) (baseStart_2387871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387871 prefixEnd_2387871 := by exact prefixLift 2387871
  have htrace : WordTrace (prefixWord ++ tailWord_2387871) baseStart_2387871 baseEnd_2387871 := by
    simpa [prefixWord, tailWord_2387871, baseEnd_2387871] using wordTrace_append hprefix tailTrace_2387871
  have hstable : (prefixWord ++ tailWord_2387871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387871).length < 2 ^ (prefixWord ++ tailWord_2387871).sum := by decide
  have hdescent : baseEnd_2387871 < baseStart_2387871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2387901 : List Nat := [1, 4, 1, 2, 3, 2, 3, 1, 2, 3]
def baseStart_2387901 : Nat := 118140960795 + 2387901 * 2 ^ 59
def prefixEnd_2387901 : Nat := 4983230072969 + 3 ^ 40 * 2387901 * 2
def baseEnd_2387901 : Nat := 817427312234644706703833

theorem tailTrace_2387901 : CollatzResearch.WordTrace tailWord_2387901 prefixEnd_2387901 817427312234644706703833 := by
  unfold tailWord_2387901
  simp only [CollatzResearch.WordTrace]
  refine ⟨87093904522049972867619557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58062603014699981911746371 87093904522049972867619557)
  ·
    refine ⟨16330107097884369912678667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 87093904522049972867619557 16330107097884369912678667)
    ·
      refine ⟨24495160646826554869018001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16330107097884369912678667 24495160646826554869018001)
      ·
        refine ⟨18371370485119916151763501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24495160646826554869018001 18371370485119916151763501)
        ·
          refine ⟨6889263931919968556911313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18371370485119916151763501 6889263931919968556911313)
          ·
            refine ⟨5166947948939976417683485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6889263931919968556911313 5166947948939976417683485)
            ·
              refine ⟨1937605480852491156631307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5166947948939976417683485 1937605480852491156631307)
              ·
                refine ⟨2906408221278736734946961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1937605480852491156631307 2906408221278736734946961)
                ·
                  refine ⟨2179806165959052551210221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2906408221278736734946961 2179806165959052551210221)
                  ·
                    refine ⟨817427312234644706703833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2179806165959052551210221 817427312234644706703833)
                    ·
                      rfl

theorem cell22_2387901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 1, 2, 3].length) (baseStart_2387901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2387901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2387901 prefixEnd_2387901 := by exact prefixLift 2387901
  have htrace : WordTrace (prefixWord ++ tailWord_2387901) baseStart_2387901 baseEnd_2387901 := by
    simpa [prefixWord, tailWord_2387901, baseEnd_2387901] using wordTrace_append hprefix tailTrace_2387901
  have hstable : (prefixWord ++ tailWord_2387901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2387901).length < 2 ^ (prefixWord ++ tailWord_2387901).sum := by decide
  have hdescent : baseEnd_2387901 < baseStart_2387901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2387901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388002 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_2388002 : Nat := 118140960795 + 2388002 * 2 ^ 59
def prefixEnd_2388002 : Nat := 4983230072969 + 3 ^ 40 * 2388002 * 2
def baseEnd_2388002 : Nat := 817461886598714109928523

theorem tailTrace_2388002 : CollatzResearch.WordTrace tailWord_2388002 prefixEnd_2388002 817461886598714109928523 := by
  unfold tailWord_2388002
  simp only [CollatzResearch.WordTrace]
  refine ⟨21774397073671016779261565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58065058863122711411364173 21774397073671016779261565)
  ·
    refine ⟨8165398902626631292223087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21774397073671016779261565 8165398902626631292223087)
    ·
      refine ⟨12248098353939946938334631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8165398902626631292223087 12248098353939946938334631)
      ·
        refine ⟨18372147530909920407501947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12248098353939946938334631 18372147530909920407501947)
        ·
          refine ⟨27558221296364880611252921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18372147530909920407501947 27558221296364880611252921)
          ·
            refine ⟨20668665972273660458439691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27558221296364880611252921 20668665972273660458439691)
            ·
              refine ⟨31002998958410490687659537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20668665972273660458439691 31002998958410490687659537)
              ·
                refine ⟨23252249218807868015744653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31002998958410490687659537 23252249218807868015744653)
                ·
                  refine ⟨8719593457052950505904245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23252249218807868015744653 8719593457052950505904245)
                  ·
                    refine ⟨817461886598714109928523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8719593457052950505904245 817461886598714109928523)
                    ·
                      rfl

theorem cell22_2388002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_2388002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388002 prefixEnd_2388002 := by exact prefixLift 2388002
  have htrace : WordTrace (prefixWord ++ tailWord_2388002) baseStart_2388002 baseEnd_2388002 := by
    simpa [prefixWord, tailWord_2388002, baseEnd_2388002] using wordTrace_append hprefix tailTrace_2388002
  have hstable : (prefixWord ++ tailWord_2388002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388002).length < 2 ^ (prefixWord ++ tailWord_2388002).sum := by decide
  have hdescent : baseEnd_2388002 < baseStart_2388002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388015 : List Nat := [1, 1, 2, 1, 2, 1, 1, 13]
def baseStart_2388015 : Nat := 118140960795 + 2388015 * 2 ^ 59
def prefixEnd_2388015 : Nat := 4983230072969 + 3 ^ 40 * 2388015 * 2
def baseEnd_2388015 : Nat := 90829592973820712150387

theorem tailTrace_2388015 : CollatzResearch.WordTrace tailWord_2388015 prefixEnd_2388015 90829592973820712150387 := by
  unfold tailWord_2388015
  simp only [CollatzResearch.WordTrace]
  refine ⟨87098062443636970337269499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58065374962424646891512999 87098062443636970337269499)
  ·
    refine ⟨130647093665455455505904249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87098062443636970337269499 130647093665455455505904249)
    ·
      refine ⟨97985320249091591629428187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130647093665455455505904249 97985320249091591629428187)
      ·
        refine ⟨146977980373637387444142281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97985320249091591629428187 146977980373637387444142281)
        ·
          refine ⟨110233485280228040583106711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 146977980373637387444142281 110233485280228040583106711)
          ·
            refine ⟨165350227920342060874660067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 110233485280228040583106711 165350227920342060874660067)
            ·
              refine ⟨248025341880513091311990101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 165350227920342060874660067 248025341880513091311990101)
              ·
                refine ⟨90829592973820712150387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 248025341880513091311990101 90829592973820712150387)
                ·
                  rfl

theorem cell22_2388015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 13].length) (baseStart_2388015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388015 prefixEnd_2388015 := by exact prefixLift 2388015
  have htrace : WordTrace (prefixWord ++ tailWord_2388015) baseStart_2388015 baseEnd_2388015 := by
    simpa [prefixWord, tailWord_2388015, baseEnd_2388015] using wordTrace_append hprefix tailTrace_2388015
  have hstable : (prefixWord ++ tailWord_2388015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388015).length < 2 ^ (prefixWord ++ tailWord_2388015).sum := by decide
  have hdescent : baseEnd_2388015 < baseStart_2388015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388019 : List Nat := [1, 1, 1, 2, 4, 1, 4, 3, 2, 3]
def baseStart_2388019 : Nat := 118140960795 + 2388019 * 2 ^ 59
def prefixEnd_2388019 : Nat := 4983230072969 + 3 ^ 40 * 2388019 * 2
def baseEnd_2388019 : Nat := 817467706046131732253471

theorem tailTrace_2388019 : CollatzResearch.WordTrace tailWord_2388019 prefixEnd_2388019 817467706046131732253471 := by
  unfold tailWord_2388019
  simp only [CollatzResearch.WordTrace]
  refine ⟨87098208335622479020415111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58065472223748319346943407 87098208335622479020415111)
  ·
    refine ⟨130647312503433718530622667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87098208335622479020415111 130647312503433718530622667)
    ·
      refine ⟨195970968755150577795934001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130647312503433718530622667 195970968755150577795934001)
      ·
        refine ⟨146978226566362933346950501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 195970968755150577795934001 146978226566362933346950501)
        ·
          refine ⟨27558417481193050002553219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 146978226566362933346950501 27558417481193050002553219)
          ·
            refine ⟨41337626221789575003829829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27558417481193050002553219 41337626221789575003829829)
            ·
              refine ⟨7750804916585545313218093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41337626221789575003829829 7750804916585545313218093)
              ·
                refine ⟨2906551843719579492456785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7750804916585545313218093 2906551843719579492456785)
                ·
                  refine ⟨2179913882789684619342589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2906551843719579492456785 2179913882789684619342589)
                  ·
                    refine ⟨817467706046131732253471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2179913882789684619342589 817467706046131732253471)
                    ·
                      rfl

theorem cell22_2388019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 3].length) (baseStart_2388019 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388019 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388019 prefixEnd_2388019 := by exact prefixLift 2388019
  have htrace : WordTrace (prefixWord ++ tailWord_2388019) baseStart_2388019 baseEnd_2388019 := by
    simpa [prefixWord, tailWord_2388019, baseEnd_2388019] using wordTrace_append hprefix tailTrace_2388019
  have hstable : (prefixWord ++ tailWord_2388019).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388019).length < 2 ^ (prefixWord ++ tailWord_2388019).sum := by decide
  have hdescent : baseEnd_2388019 < baseStart_2388019 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388038 : List Nat := [6, 1, 1, 1, 1, 1, 4, 3, 4]
def baseStart_2388038 : Nat := 118140960795 + 2388038 * 2 ^ 59
def prefixEnd_2388038 : Nat := 4983230072969 + 3 ^ 40 * 2388038 * 2
def baseEnd_2388038 : Nat := 272491403378140672009471

theorem tailTrace_2388038 : CollatzResearch.WordTrace tailWord_2388038 prefixEnd_2388038 272491403378140672009471 := by
  unfold tailWord_2388038
  simp only [CollatzResearch.WordTrace]
  refine ⟨2721840666329801414542399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58065934215035763510237845 2721840666329801414542399)
  ·
    refine ⟨4082760999494702121813599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2721840666329801414542399 4082760999494702121813599)
    ·
      refine ⟨6124141499242053182720399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4082760999494702121813599 6124141499242053182720399)
      ·
        refine ⟨9186212248863079774080599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6124141499242053182720399 9186212248863079774080599)
        ·
          refine ⟨13779318373294619661120899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9186212248863079774080599 13779318373294619661120899)
          ·
            refine ⟨20668977559941929491681349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13779318373294619661120899 20668977559941929491681349)
            ·
              refine ⟨3875433292489111779690253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 20668977559941929491681349 3875433292489111779690253)
              ·
                refine ⟨1453287484683416917383845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3875433292489111779690253 1453287484683416917383845)
                ·
                  refine ⟨272491403378140672009471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453287484683416917383845 272491403378140672009471)
                  ·
                    rfl

theorem cell22_2388038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_2388038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388038 prefixEnd_2388038 := by exact prefixLift 2388038
  have htrace : WordTrace (prefixWord ++ tailWord_2388038) baseStart_2388038 baseEnd_2388038 := by
    simpa [prefixWord, tailWord_2388038, baseEnd_2388038] using wordTrace_append hprefix tailTrace_2388038
  have hstable : (prefixWord ++ tailWord_2388038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388038).length < 2 ^ (prefixWord ++ tailWord_2388038).sum := by decide
  have hdescent : baseEnd_2388038 < baseStart_2388038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388064 : List Nat := [2, 1, 1, 3, 2, 3, 1, 3, 3, 3]
def baseStart_2388064 : Nat := 118140960795 + 2388064 * 2 ^ 59
def prefixEnd_2388064 : Nat := 4983230072969 + 3 ^ 40 * 2388064 * 2
def baseEnd_2388064 : Nat := 817483110465766614878333

theorem tailTrace_2388064 : CollatzResearch.WordTrace tailWord_2388064 prefixEnd_2388064 817483110465766614878333 := by
  unfold tailWord_2388064
  simp only [CollatzResearch.WordTrace]
  refine ⟨43549924810229725852901623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58066566413639634470535497 43549924810229725852901623)
  ·
    refine ⟨65324887215344588779352435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43549924810229725852901623 65324887215344588779352435)
    ·
      refine ⟨97987330823016883169028653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65324887215344588779352435 97987330823016883169028653)
      ·
        refine ⟨36745249058631331188385745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97987330823016883169028653 36745249058631331188385745)
        ·
          refine ⟨27558936793973498391289309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36745249058631331188385745 27558936793973498391289309)
          ·
            refine ⟨10334601297740061896733491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 27558936793973498391289309 10334601297740061896733491)
            ·
              refine ⟨15501901946610092845100237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10334601297740061896733491 15501901946610092845100237)
              ·
                refine ⟨5813213229978784816912589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15501901946610092845100237 5813213229978784816912589)
                ·
                  refine ⟨2179954961242044306342221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5813213229978784816912589 2179954961242044306342221)
                  ·
                    refine ⟨817483110465766614878333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2179954961242044306342221 817483110465766614878333)
                    ·
                      rfl

theorem cell22_2388064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 3, 3, 3].length) (baseStart_2388064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388064 prefixEnd_2388064 := by exact prefixLift 2388064
  have htrace : WordTrace (prefixWord ++ tailWord_2388064) baseStart_2388064 baseEnd_2388064 := by
    simpa [prefixWord, tailWord_2388064, baseEnd_2388064] using wordTrace_append hprefix tailTrace_2388064
  have hstable : (prefixWord ++ tailWord_2388064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388064).length < 2 ^ (prefixWord ++ tailWord_2388064).sum := by decide
  have hdescent : baseEnd_2388064 < baseStart_2388064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388107 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 7, 4]
def baseStart_2388107 : Nat := 118140960795 + 2388107 * 2 ^ 59
def prefixEnd_2388107 : Nat := 4983230072969 + 3 ^ 40 * 2388107 * 2
def baseEnd_2388107 : Nat := 817497830244528836053201

theorem tailTrace_2388107 : CollatzResearch.WordTrace tailWord_2388107 prefixEnd_2388107 817497830244528836053201 := by
  unfold tailWord_2388107
  simp only [CollatzResearch.WordTrace]
  refine ⟨87101417959303670049618575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58067611972869113366412383 87101417959303670049618575)
  ·
    refine ⟨130652126938955505074427863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87101417959303670049618575 130652126938955505074427863)
    ·
      refine ⟨195978190408433257611641795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130652126938955505074427863 195978190408433257611641795)
      ·
        refine ⟨293967285612649886417462693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195978190408433257611641795 293967285612649886417462693)
        ·
          refine ⟨55118866052371853703274255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 293967285612649886417462693 55118866052371853703274255)
          ·
            refine ⟨82678299078557780554911383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55118866052371853703274255 82678299078557780554911383)
            ·
              refine ⟨124017448617836670832367075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 82678299078557780554911383 124017448617836670832367075)
              ·
                refine ⟨186026172926755006248550613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 124017448617836670832367075 186026172926755006248550613)
                ·
                  refine ⟨4359988427970820458950405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 186026172926755006248550613 4359988427970820458950405)
                  ·
                    refine ⟨817497830244528836053201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4359988427970820458950405 817497830244528836053201)
                    ·
                      rfl

theorem cell22_2388107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 4].length) (baseStart_2388107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388107 prefixEnd_2388107 := by exact prefixLift 2388107
  have htrace : WordTrace (prefixWord ++ tailWord_2388107) baseStart_2388107 baseEnd_2388107 := by
    simpa [prefixWord, tailWord_2388107, baseEnd_2388107] using wordTrace_append hprefix tailTrace_2388107
  have hstable : (prefixWord ++ tailWord_2388107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388107).length < 2 ^ (prefixWord ++ tailWord_2388107).sum := by decide
  have hdescent : baseEnd_2388107 < baseStart_2388107 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388124 : List Nat := [2, 2, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_2388124 : Nat := 118140960795 + 2388124 * 2 ^ 59
def prefixEnd_2388124 : Nat := 4983230072969 + 3 ^ 40 * 2388124 * 2
def baseEnd_2388124 : Nat := 817503649691946458378149

theorem tailTrace_2388124 : CollatzResearch.WordTrace tailWord_2388124 prefixEnd_2388124 817503649691946458378149 := by
  unfold tailWord_2388124
  simp only [CollatzResearch.WordTrace]
  refine ⟨43551019000121040976493713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58068025333494721301991617 43551019000121040976493713)
  ·
    refine ⟨32663264250090780732370285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43551019000121040976493713 32663264250090780732370285)
    ·
      refine ⟨12248724093784042774638857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32663264250090780732370285 12248724093784042774638857)
      ·
        refine ⟨9186543070338032080979143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12248724093784042774638857 9186543070338032080979143)
        ·
          refine ⟨13779814605507048121468715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9186543070338032080979143 13779814605507048121468715)
          ·
            refine ⟨20669721908260572182203073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13779814605507048121468715 20669721908260572182203073)
            ·
              refine ⟨15502291431195429136652305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20669721908260572182203073 15502291431195429136652305)
              ·
                refine ⟨11626718573396571852489229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15502291431195429136652305 11626718573396571852489229)
                ·
                  refine ⟨4360019465023714444683461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11626718573396571852489229 4360019465023714444683461)
                  ·
                    refine ⟨817503649691946458378149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4360019465023714444683461 817503649691946458378149)
                    ·
                      rfl

theorem cell22_2388124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_2388124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388124 prefixEnd_2388124 := by exact prefixLift 2388124
  have htrace : WordTrace (prefixWord ++ tailWord_2388124) baseStart_2388124 baseEnd_2388124 := by
    simpa [prefixWord, tailWord_2388124, baseEnd_2388124] using wordTrace_append hprefix tailTrace_2388124
  have hstable : (prefixWord ++ tailWord_2388124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388124).length < 2 ^ (prefixWord ++ tailWord_2388124).sum := by decide
  have hdescent : baseEnd_2388124 < baseStart_2388124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388141 : List Nat := [1, 5, 2, 1, 2, 2, 1, 1, 3, 4]
def baseStart_2388141 : Nat := 118140960795 + 2388141 * 2 ^ 59
def prefixEnd_2388141 : Nat := 4983230072969 + 3 ^ 40 * 2388141 * 2
def baseEnd_2388141 : Nat := 817509469139364080703097

theorem tailTrace_2388141 : CollatzResearch.WordTrace tailWord_2388141 prefixEnd_2388141 817509469139364080703097 := by
  unfold tailWord_2388141
  simp only [CollatzResearch.WordTrace]
  refine ⟨87102658041180493856356277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58068438694120329237570851 87102658041180493856356277)
  ·
    refine ⟨8165874191360671299033401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87102658041180493856356277 8165874191360671299033401)
    ·
      refine ⟨6124405643520503474275051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8165874191360671299033401 6124405643520503474275051)
      ·
        refine ⟨9186608465280755211412577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6124405643520503474275051 9186608465280755211412577)
        ·
          refine ⟨6889956348960566408559433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9186608465280755211412577 6889956348960566408559433)
          ·
            refine ⟨5167467261720424806419575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6889956348960566408559433 5167467261720424806419575)
            ·
              refine ⟨7751200892580637209629363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167467261720424806419575 7751200892580637209629363)
              ·
                refine ⟨11626801338870955814444045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7751200892580637209629363 11626801338870955814444045)
                ·
                  refine ⟨4360050502076608430416517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11626801338870955814444045 4360050502076608430416517)
                  ·
                    refine ⟨817509469139364080703097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4360050502076608430416517 817509469139364080703097)
                    ·
                      rfl

theorem cell22_2388141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_2388141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388141 prefixEnd_2388141 := by exact prefixLift 2388141
  have htrace : WordTrace (prefixWord ++ tailWord_2388141) baseStart_2388141 baseEnd_2388141 := by
    simpa [prefixWord, tailWord_2388141, baseEnd_2388141] using wordTrace_append hprefix tailTrace_2388141
  have hstable : (prefixWord ++ tailWord_2388141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388141).length < 2 ^ (prefixWord ++ tailWord_2388141).sum := by decide
  have hdescent : baseEnd_2388141 < baseStart_2388141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388154 : List Nat := [3, 1, 1, 1, 2, 2, 2, 1, 6, 3]
def baseStart_2388154 : Nat := 118140960795 + 2388154 * 2 ^ 59
def prefixEnd_2388154 : Nat := 4983230072969 + 3 ^ 40 * 2388154 * 2
def baseEnd_2388154 : Nat := 817513919305036380128057

theorem tailTrace_2388154 : CollatzResearch.WordTrace tailWord_2388154 prefixEnd_2388154 817513919305036380128057 := by
  unfold tailWord_2388154
  simp only [CollatzResearch.WordTrace]
  refine ⟨21775783047533349269144879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58068754793422264717719677 21775783047533349269144879)
  ·
    refine ⟨32663674571300023903717319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21775783047533349269144879 32663674571300023903717319)
    ·
      refine ⟨48995511856950035855575979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32663674571300023903717319 48995511856950035855575979)
      ·
        refine ⟨73493267785425053783363969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48995511856950035855575979 73493267785425053783363969)
        ·
          refine ⟨55119950839068790337522977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73493267785425053783363969 55119950839068790337522977)
          ·
            refine ⟨41339963129301592753142233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55119950839068790337522977 41339963129301592753142233)
            ·
              refine ⟨31004972346976194564856675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41339963129301592753142233 31004972346976194564856675)
              ·
                refine ⟨46507458520464291847285013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31004972346976194564856675 46507458520464291847285013)
                ·
                  refine ⟨2180037118146763680341485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 46507458520464291847285013 2180037118146763680341485)
                  ·
                    refine ⟨817513919305036380128057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2180037118146763680341485 817513919305036380128057)
                    ·
                      rfl

theorem cell22_2388154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 1, 6, 3].length) (baseStart_2388154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388154 prefixEnd_2388154 := by exact prefixLift 2388154
  have htrace : WordTrace (prefixWord ++ tailWord_2388154) baseStart_2388154 baseEnd_2388154 := by
    simpa [prefixWord, tailWord_2388154, baseEnd_2388154] using wordTrace_append hprefix tailTrace_2388154
  have hstable : (prefixWord ++ tailWord_2388154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388154).length < 2 ^ (prefixWord ++ tailWord_2388154).sum := by decide
  have hdescent : baseEnd_2388154 < baseStart_2388154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388171 : List Nat := [1, 1, 1, 1, 3, 2, 6, 2, 2, 3]
def baseStart_2388171 : Nat := 118140960795 + 2388171 * 2 ^ 59
def prefixEnd_2388171 : Nat := 4983230072969 + 3 ^ 40 * 2388171 * 2
def baseEnd_2388171 : Nat := 817519738752454002453005

theorem tailTrace_2388171 : CollatzResearch.WordTrace tailWord_2388171 prefixEnd_2388171 817519738752454002453005 := by
  unfold tailWord_2388171
  simp only [CollatzResearch.WordTrace]
  refine ⟨87103752231071808979948367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58069168154047872653298911 87103752231071808979948367)
  ·
    refine ⟨130655628346607713469922551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87103752231071808979948367 130655628346607713469922551)
    ·
      refine ⟨195983442519911570204883827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130655628346607713469922551 195983442519911570204883827)
      ·
        refine ⟨293975163779867355307325741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 195983442519911570204883827 293975163779867355307325741)
        ·
          refine ⟨110240686417450258240247153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 293975163779867355307325741 110240686417450258240247153)
          ·
            refine ⟨82680514813087693680185365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 110240686417450258240247153 82680514813087693680185365)
            ·
              refine ⟨3875649131863485641258689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 82680514813087693680185365 3875649131863485641258689)
              ·
                refine ⟨2906736848897614230944017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3875649131863485641258689 2906736848897614230944017)
                ·
                  refine ⟨2180052636673210673208013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2906736848897614230944017 2180052636673210673208013)
                  ·
                    refine ⟨817519738752454002453005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2180052636673210673208013 817519738752454002453005)
                    ·
                      rfl

theorem cell22_2388171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 2, 2, 3].length) (baseStart_2388171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388171 prefixEnd_2388171 := by exact prefixLift 2388171
  have htrace : WordTrace (prefixWord ++ tailWord_2388171) baseStart_2388171 baseEnd_2388171 := by
    simpa [prefixWord, tailWord_2388171, baseEnd_2388171] using wordTrace_append hprefix tailTrace_2388171
  have hstable : (prefixWord ++ tailWord_2388171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388171).length < 2 ^ (prefixWord ++ tailWord_2388171).sum := by decide
  have hdescent : baseEnd_2388171 < baseStart_2388171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388184 : List Nat := [2, 1, 2, 2, 4, 1, 3, 7]
def baseStart_2388184 : Nat := 118140960795 + 2388184 * 2 ^ 59
def prefixEnd_2388184 : Nat := 4983230072969 + 3 ^ 40 * 2388184 * 2
def baseEnd_2388184 : Nat := 90836020990902922430885

theorem tailTrace_2388184 : CollatzResearch.WordTrace tailWord_2388184 prefixEnd_2388184 90836020990902922430885 := by
  unfold tailWord_2388184
  simp only [CollatzResearch.WordTrace]
  refine ⟨43552113190012356100085803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58069484253349808133447737 43552113190012356100085803)
  ·
    refine ⟨65328169785018534150128705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43552113190012356100085803 65328169785018534150128705)
    ·
      refine ⟨48996127338763900612596529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65328169785018534150128705 48996127338763900612596529)
      ·
        refine ⟨36747095504072925459447397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 48996127338763900612596529 36747095504072925459447397)
        ·
          refine ⟨6890080407013673523646387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 36747095504072925459447397 6890080407013673523646387)
          ·
            refine ⟨10335120610520510285469581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6890080407013673523646387 10335120610520510285469581)
            ·
              refine ⟨3875670228945191357051093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10335120610520510285469581 3875670228945191357051093)
              ·
                refine ⟨90836020990902922430885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3875670228945191357051093 90836020990902922430885)
                ·
                  rfl

theorem cell22_2388184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 7].length) (baseStart_2388184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388184 prefixEnd_2388184 := by exact prefixLift 2388184
  have htrace : WordTrace (prefixWord ++ tailWord_2388184) baseStart_2388184 baseEnd_2388184 := by
    simpa [prefixWord, tailWord_2388184, baseEnd_2388184] using wordTrace_append hprefix tailTrace_2388184
  have hstable : (prefixWord ++ tailWord_2388184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388184).length < 2 ^ (prefixWord ++ tailWord_2388184).sum := by decide
  have hdescent : baseEnd_2388184 < baseStart_2388184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388229 : List Nat := [1, 3, 1, 1, 2, 1, 2, 6, 5]
def baseStart_2388229 : Nat := 118140960795 + 2388229 * 2 ^ 59
def prefixEnd_2388229 : Nat := 4983230072969 + 3 ^ 40 * 2388229 * 2
def baseEnd_2388229 : Nat := 272513197779253728167609

theorem tailTrace_2388229 : CollatzResearch.WordTrace tailWord_2388229 prefixEnd_2388229 272513197779253728167609 := by
  unfold tailWord_2388229
  simp only [CollatzResearch.WordTrace]
  refine ⟨87105867664861684885559741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58070578443241123257039827 87105867664861684885559741)
  ·
    refine ⟨32664700374323131832084903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87105867664861684885559741 32664700374323131832084903)
    ·
      refine ⟨48997050561484697748127355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32664700374323131832084903 48997050561484697748127355)
      ·
        refine ⟨73495575842227046622191033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 48997050561484697748127355 73495575842227046622191033)
        ·
          refine ⟨55121681881670284966643275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73495575842227046622191033 55121681881670284966643275)
          ·
            refine ⟨82682522822505427449964913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55121681881670284966643275 82682522822505427449964913)
            ·
              refine ⟨62011892116879070587473685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82682522822505427449964913 62011892116879070587473685)
              ·
                refine ⟨2906807442978706433787829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62011892116879070587473685 2906807442978706433787829)
                ·
                  refine ⟨272513197779253728167609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2906807442978706433787829 272513197779253728167609)
                  ·
                    rfl

theorem cell22_2388229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 6, 5].length) (baseStart_2388229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388229 prefixEnd_2388229 := by exact prefixLift 2388229
  have htrace : WordTrace (prefixWord ++ tailWord_2388229) baseStart_2388229 baseEnd_2388229 := by
    simpa [prefixWord, tailWord_2388229, baseEnd_2388229] using wordTrace_append hprefix tailTrace_2388229
  have hstable : (prefixWord ++ tailWord_2388229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388229).length < 2 ^ (prefixWord ++ tailWord_2388229).sum := by decide
  have hdescent : baseEnd_2388229 < baseStart_2388229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388233 : List Nat := [1, 2, 1, 1, 3, 4, 2, 4, 1, 3]
def baseStart_2388233 : Nat := 118140960795 + 2388233 * 2 ^ 59
def prefixEnd_2388233 : Nat := 4983230072969 + 3 ^ 40 * 2388233 * 2
def baseEnd_2388233 : Nat := 817540962619506507402815

theorem tailTrace_2388233 : CollatzResearch.WordTrace tailWord_2388233 prefixEnd_2388233 817540962619506507402815 := by
  unfold tailWord_2388233
  simp only [CollatzResearch.WordTrace]
  refine ⟨87106013556847193568705353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58070675704564795712470235 87106013556847193568705353)
  ·
    refine ⟨65329510167635395176529015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87106013556847193568705353 65329510167635395176529015)
    ·
      refine ⟨97994265251453092764793523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65329510167635395176529015 97994265251453092764793523)
      ·
        refine ⟨146991397877179639147190285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 97994265251453092764793523 146991397877179639147190285)
        ·
          refine ⟨55121774203942364680196357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 146991397877179639147190285 55121774203942364680196357)
          ·
            refine ⟨10335332663239193377536817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 55121774203942364680196357 10335332663239193377536817)
            ·
              refine ⟨7751499497429395033152613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10335332663239193377536817 7751499497429395033152613)
              ·
                refine ⟨1453406155768011568716115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7751499497429395033152613 1453406155768011568716115)
                ·
                  refine ⟨2180109233652017353074173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1453406155768011568716115 2180109233652017353074173)
                  ·
                    refine ⟨817540962619506507402815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2180109233652017353074173 817540962619506507402815)
                    ·
                      rfl

theorem cell22_2388233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 2, 4, 1, 3].length) (baseStart_2388233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388233 prefixEnd_2388233 := by exact prefixLift 2388233
  have htrace : WordTrace (prefixWord ++ tailWord_2388233) baseStart_2388233 baseEnd_2388233 := by
    simpa [prefixWord, tailWord_2388233, baseEnd_2388233] using wordTrace_append hprefix tailTrace_2388233
  have hstable : (prefixWord ++ tailWord_2388233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388233).length < 2 ^ (prefixWord ++ tailWord_2388233).sum := by decide
  have hdescent : baseEnd_2388233 < baseStart_2388233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388291 : List Nat := [1, 1, 1, 3, 1, 3, 2, 6, 4]
def baseStart_2388291 : Nat := 118140960795 + 2388291 * 2 ^ 59
def prefixEnd_2388291 : Nat := 4983230072969 + 3 ^ 40 * 2388291 * 2
def baseEnd_2388291 : Nat := 272520272401604563150879

theorem tailTrace_2388291 : CollatzResearch.WordTrace tailWord_2388291 prefixEnd_2388291 272520272401604563150879 := by
  unfold tailWord_2388291
  simp only [CollatzResearch.WordTrace]
  refine ⟨87108128990637069474316727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58072085993758046316211151 87108128990637069474316727)
  ·
    refine ⟨130662193485955604211475091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87108128990637069474316727 130662193485955604211475091)
    ·
      refine ⟨195993290228933406317212637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130662193485955604211475091 195993290228933406317212637)
      ·
        refine ⟨73497483835850027368954739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 195993290228933406317212637 73497483835850027368954739)
        ·
          refine ⟨110246225753775041053432109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73497483835850027368954739 110246225753775041053432109)
          ·
            refine ⟨41342334657665640395037041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110246225753775041053432109 41342334657665640395037041)
            ·
              refine ⟨31006750993249230296277781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41342334657665640395037041 31006750993249230296277781)
              ·
                refine ⟨1453441452808557670138021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 31006750993249230296277781 1453441452808557670138021)
                ·
                  refine ⟨272520272401604563150879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453441452808557670138021 272520272401604563150879)
                  ·
                    rfl

theorem cell22_2388291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 6, 4].length) (baseStart_2388291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388291 prefixEnd_2388291 := by exact prefixLift 2388291
  have htrace : WordTrace (prefixWord ++ tailWord_2388291) baseStart_2388291 baseEnd_2388291 := by
    simpa [prefixWord, tailWord_2388291, baseEnd_2388291] using wordTrace_append hprefix tailTrace_2388291
  have hstable : (prefixWord ++ tailWord_2388291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388291).length < 2 ^ (prefixWord ++ tailWord_2388291).sum := by decide
  have hdescent : baseEnd_2388291 < baseStart_2388291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388319 : List Nat := [1, 1, 2, 3, 1, 2, 4, 8]
def baseStart_2388319 : Nat := 118140960795 + 2388319 * 2 ^ 59
def prefixEnd_2388319 : Nat := 4983230072969 + 3 ^ 40 * 2388319 * 2
def baseEnd_2388319 : Nat := 90841155797447883305839

theorem tailTrace_2388319 : CollatzResearch.WordTrace tailWord_2388319 prefixEnd_2388319 90841155797447883305839 := by
  unfold tailWord_2388319
  simp only [CollatzResearch.WordTrace]
  refine ⟨87109150234535630256336011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58072766823023753504224007 87109150234535630256336011)
  ·
    refine ⟨130663725351803445384504017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87109150234535630256336011 130663725351803445384504017)
    ·
      refine ⟨97997794013852584038378013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130663725351803445384504017 97997794013852584038378013)
      ·
        refine ⟨36749172755194719014391755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 97997794013852584038378013 36749172755194719014391755)
        ·
          refine ⟨55123759132792078521587633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36749172755194719014391755 55123759132792078521587633)
          ·
            refine ⟨41342819349594058891190725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55123759132792078521587633 41342819349594058891190725)
            ·
              refine ⟨7751778628048886042098261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 41342819349594058891190725 7751778628048886042098261)
              ·
                refine ⟨90841155797447883305839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7751778628048886042098261 90841155797447883305839)
                ·
                  rfl

theorem cell22_2388319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 8].length) (baseStart_2388319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388319 prefixEnd_2388319 := by exact prefixLift 2388319
  have htrace : WordTrace (prefixWord ++ tailWord_2388319) baseStart_2388319 baseEnd_2388319 := by
    simpa [prefixWord, tailWord_2388319, baseEnd_2388319] using wordTrace_append hprefix tailTrace_2388319
  have hstable : (prefixWord ++ tailWord_2388319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388319).length < 2 ^ (prefixWord ++ tailWord_2388319).sum := by decide
  have hdescent : baseEnd_2388319 < baseStart_2388319 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388342 : List Nat := [5, 1, 1, 4, 1, 1, 1, 4, 4]
def baseStart_2388342 : Nat := 118140960795 + 2388342 * 2 ^ 59
def prefixEnd_2388342 : Nat := 4983230072969 + 3 ^ 40 * 2388342 * 2
def baseEnd_2388342 : Nat := 272526091849022185475827

theorem tailTrace_2388342 : CollatzResearch.WordTrace tailWord_2388342 prefixEnd_2388342 272526091849022185475827 := by
  unfold tailWord_2388342
  simp only [CollatzResearch.WordTrace]
  refine ⟨5444374319590769074026455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58073326075634870122948853 5444374319590769074026455)
  ·
    refine ⟨8166561479386153611039683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5444374319590769074026455 8166561479386153611039683)
    ·
      refine ⟨12249842219079230416559525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8166561479386153611039683 12249842219079230416559525)
      ·
        refine ⟨2296845416077355703104911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12249842219079230416559525 2296845416077355703104911)
        ·
          refine ⟨3445268124116033554657367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2296845416077355703104911 3445268124116033554657367)
          ·
            refine ⟨5167902186174050331986051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445268124116033554657367 5167902186174050331986051)
            ·
              refine ⟨7751853279261075497979077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5167902186174050331986051 7751853279261075497979077)
              ·
                refine ⟨1453472489861451655871077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7751853279261075497979077 1453472489861451655871077)
                ·
                  refine ⟨272526091849022185475827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453472489861451655871077 272526091849022185475827)
                  ·
                    rfl

theorem cell22_2388342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_2388342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388342 prefixEnd_2388342 := by exact prefixLift 2388342
  have htrace : WordTrace (prefixWord ++ tailWord_2388342) baseStart_2388342 baseEnd_2388342 := by
    simpa [prefixWord, tailWord_2388342, baseEnd_2388342] using wordTrace_append hprefix tailTrace_2388342
  have hstable : (prefixWord ++ tailWord_2388342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388342).length < 2 ^ (prefixWord ++ tailWord_2388342).sum := by decide
  have hdescent : baseEnd_2388342 < baseStart_2388342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388353 : List Nat := [1, 2, 4, 3, 1, 3, 1, 7]
def baseStart_2388353 : Nat := 118140960795 + 2388353 * 2 ^ 59
def prefixEnd_2388353 : Nat := 4983230072969 + 3 ^ 40 * 2388353 * 2
def baseEnd_2388353 : Nat := 90842449007985132711383

theorem tailTrace_2388353 : CollatzResearch.WordTrace tailWord_2388353 prefixEnd_2388353 90842449007985132711383 := by
  unfold tailWord_2388353
  simp only [CollatzResearch.WordTrace]
  refine ⟨87110390316412454063073713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58073593544274969375382475 87110390316412454063073713)
  ·
    refine ⟨65332792737309340547305285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87110390316412454063073713 65332792737309340547305285)
    ·
      refine ⟨12249898638245501352619741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 65332792737309340547305285 12249898638245501352619741)
      ·
        refine ⟨4593711989342063007232403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12249898638245501352619741 4593711989342063007232403)
        ·
          refine ⟨6890567984013094510848605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4593711989342063007232403 6890567984013094510848605)
          ·
            refine ⟨2583962994004910441568227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6890567984013094510848605 2583962994004910441568227)
            ·
              refine ⟨3875944491007365662352341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583962994004910441568227 3875944491007365662352341)
              ·
                refine ⟨90842449007985132711383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3875944491007365662352341 90842449007985132711383)
                ·
                  rfl

theorem cell22_2388353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 7].length) (baseStart_2388353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388353 prefixEnd_2388353 := by exact prefixLift 2388353
  have htrace : WordTrace (prefixWord ++ tailWord_2388353) baseStart_2388353 baseEnd_2388353 := by
    simpa [prefixWord, tailWord_2388353, baseEnd_2388353] using wordTrace_append hprefix tailTrace_2388353
  have hstable : (prefixWord ++ tailWord_2388353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388353).length < 2 ^ (prefixWord ++ tailWord_2388353).sum := by decide
  have hdescent : baseEnd_2388353 < baseStart_2388353 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388372 : List Nat := [2, 4, 2, 1, 4, 1, 1, 1, 2, 4]
def baseStart_2388372 : Nat := 118140960795 + 2388372 * 2 ^ 59
def prefixEnd_2388372 : Nat := 4983230072969 + 3 ^ 40 * 2388372 * 2
def baseEnd_2388372 : Nat := 817588545160156478177389

theorem tailTrace_2388372 : CollatzResearch.WordTrace tailWord_2388372 prefixEnd_2388372 817588545160156478177389 := by
  unfold tailWord_2388372
  simp only [CollatzResearch.WordTrace]
  refine ⟨43555541651671810154007685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58074055535562413538676913 43555541651671810154007685)
  ·
    refine ⟨8166664059688464403876441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43555541651671810154007685 8166664059688464403876441)
    ·
      refine ⟨6124998044766348302907331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8166664059688464403876441 6124998044766348302907331)
      ·
        refine ⟨9187497067149522454360997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6124998044766348302907331 9187497067149522454360997)
        ·
          refine ⟨1722655700090535460192687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9187497067149522454360997 1722655700090535460192687)
          ·
            refine ⟨2583983550135803190289031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1722655700090535460192687 2583983550135803190289031)
            ·
              refine ⟨3875975325203704785433547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2583983550135803190289031 3875975325203704785433547)
              ·
                refine ⟨5813962987805557178150321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3875975325203704785433547 5813962987805557178150321)
                ·
                  refine ⟨4360472240854167883612741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5813962987805557178150321 4360472240854167883612741)
                  ·
                    refine ⟨817588545160156478177389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4360472240854167883612741 817588545160156478177389)
                    ·
                      rfl

theorem cell22_2388372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_2388372 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388372 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388372 prefixEnd_2388372 := by exact prefixLift 2388372
  have htrace : WordTrace (prefixWord ++ tailWord_2388372) baseStart_2388372 baseEnd_2388372 := by
    simpa [prefixWord, tailWord_2388372, baseEnd_2388372] using wordTrace_append hprefix tailTrace_2388372
  have hstable : (prefixWord ++ tailWord_2388372).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388372).length < 2 ^ (prefixWord ++ tailWord_2388372).sum := by decide
  have hdescent : baseEnd_2388372 < baseStart_2388372 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388426 : List Nat := [3, 1, 2, 1, 2, 2, 1, 4, 6]
def baseStart_2388426 : Nat := 118140960795 + 2388426 * 2 ^ 59
def prefixEnd_2388426 : Nat := 4983230072969 + 3 ^ 40 * 2388426 * 2
def baseEnd_2388426 : Nat := 272535676821239445775741

theorem tailTrace_2388426 : CollatzResearch.WordTrace tailWord_2388426 prefixEnd_2388426 272535676821239445775741 := by
  unfold tailWord_2388426
  simp only [CollatzResearch.WordTrace]
  refine ⟨21778263211286996882620283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58075368563431991686987421 21778263211286996882620283)
  ·
    refine ⟨32667394816930495323930425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21778263211286996882620283 32667394816930495323930425)
    ·
      refine ⟨24500546112697871492947819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32667394816930495323930425 24500546112697871492947819)
      ·
        refine ⟨36750819169046807239421729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24500546112697871492947819 36750819169046807239421729)
        ·
          refine ⟨27563114376785105429566297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 36750819169046807239421729 27563114376785105429566297)
          ·
            refine ⟨20672335782588829072174723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27563114376785105429566297 20672335782588829072174723)
            ·
              refine ⟨31008503673883243608262085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20672335782588829072174723 31008503673883243608262085)
              ·
                refine ⟨5814094438853108176549141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31008503673883243608262085 5814094438853108176549141)
                ·
                  refine ⟨272535676821239445775741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5814094438853108176549141 272535676821239445775741)
                  ·
                    rfl

theorem cell22_2388426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_2388426 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388426 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388426 prefixEnd_2388426 := by exact prefixLift 2388426
  have htrace : WordTrace (prefixWord ++ tailWord_2388426) baseStart_2388426 baseEnd_2388426 := by
    simpa [prefixWord, tailWord_2388426, baseEnd_2388426] using wordTrace_append hprefix tailTrace_2388426
  have hstable : (prefixWord ++ tailWord_2388426).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388426).length < 2 ^ (prefixWord ++ tailWord_2388426).sum := by decide
  have hdescent : baseEnd_2388426 < baseStart_2388426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388441 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 3, 5]
def baseStart_2388441 : Nat := 118140960795 + 2388441 * 2 ^ 59
def prefixEnd_2388441 : Nat := 4983230072969 + 3 ^ 40 * 2388441 * 2
def baseEnd_2388441 : Nat := 817612165270263298202177

theorem tailTrace_2388441 : CollatzResearch.WordTrace tailWord_2388441 prefixEnd_2388441 817612165270263298202177 := by
  unfold tailWord_2388441
  simp only [CollatzResearch.WordTrace]
  refine ⟨87113599940093645092277177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58075733293395763394851451 87113599940093645092277177)
  ·
    refine ⟨65335199955070233819207883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87113599940093645092277177 65335199955070233819207883)
    ·
      refine ⟨98002799932605350728811825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65335199955070233819207883 98002799932605350728811825)
      ·
        refine ⟨73502099949454013046608869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98002799932605350728811825 73502099949454013046608869)
        ·
          refine ⟨13781643740522627446239163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 73502099949454013046608869 13781643740522627446239163)
          ·
            refine ⟨20672465610783941169358745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13781643740522627446239163 20672465610783941169358745)
            ·
              refine ⟨15504349208087955877019059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20672465610783941169358745 15504349208087955877019059)
              ·
                refine ⟨23256523812131933815528589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15504349208087955877019059 23256523812131933815528589)
                ·
                  refine ⟨8721196429549475180823221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23256523812131933815528589 8721196429549475180823221)
                  ·
                    refine ⟨817612165270263298202177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8721196429549475180823221 817612165270263298202177)
                    ·
                      rfl

theorem cell22_2388441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 5].length) (baseStart_2388441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388441 prefixEnd_2388441 := by exact prefixLift 2388441
  have htrace : WordTrace (prefixWord ++ tailWord_2388441) baseStart_2388441 baseEnd_2388441 := by
    simpa [prefixWord, tailWord_2388441, baseEnd_2388441] using wordTrace_append hprefix tailTrace_2388441
  have hstable : (prefixWord ++ tailWord_2388441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388441).length < 2 ^ (prefixWord ++ tailWord_2388441).sum := by decide
  have hdescent : baseEnd_2388441 < baseStart_2388441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388460 : List Nat := [2, 2, 1, 1, 2, 1, 7, 2, 4]
def baseStart_2388460 : Nat := 118140960795 + 2388460 * 2 ^ 59
def prefixEnd_2388460 : Nat := 4983230072969 + 3 ^ 40 * 2388460 * 2
def baseEnd_2388460 : Nat := 272539556452851193992373

theorem tailTrace_2388460 : CollatzResearch.WordTrace tailWord_2388460 prefixEnd_2388460 272539556452851193992373 := by
  unfold tailWord_2388460
  simp only [CollatzResearch.WordTrace]
  refine ⟨43557146463512405668609417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58076195284683207558145889 43557146463512405668609417)
  ·
    refine ⟨32667859847634304251457063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43557146463512405668609417 32667859847634304251457063)
    ·
      refine ⟨49001789771451456377185595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 32667859847634304251457063 49001789771451456377185595)
      ·
        refine ⟨73502684657177184565778393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49001789771451456377185595 73502684657177184565778393)
        ·
          refine ⟨55127013492882888424333795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73502684657177184565778393 55127013492882888424333795)
          ·
            refine ⟨82690520239324332636500693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55127013492882888424333795 82690520239324332636500693)
            ·
              refine ⟨1938059068109164046167985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 82690520239324332636500693 1938059068109164046167985)
              ·
                refine ⟨1453544301081873034625989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1938059068109164046167985 1453544301081873034625989)
                ·
                  refine ⟨272539556452851193992373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453544301081873034625989 272539556452851193992373)
                  ·
                    rfl

theorem cell22_2388460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_2388460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388460 prefixEnd_2388460 := by exact prefixLift 2388460
  have htrace : WordTrace (prefixWord ++ tailWord_2388460) baseStart_2388460 baseEnd_2388460 := by
    simpa [prefixWord, tailWord_2388460, baseEnd_2388460] using wordTrace_append hprefix tailTrace_2388460
  have hstable : (prefixWord ++ tailWord_2388460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388460).length < 2 ^ (prefixWord ++ tailWord_2388460).sum := by decide
  have hdescent : baseEnd_2388460 < baseStart_2388460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388533 : List Nat := [1, 3, 3, 1, 1, 2, 1, 5, 5]
def baseStart_2388533 : Nat := 118140960795 + 2388533 * 2 ^ 59
def prefixEnd_2388533 : Nat := 4983230072969 + 3 ^ 40 * 2388533 * 2
def baseEnd_2388533 : Nat := 272547886250135241633965

theorem tailTrace_2388533 : CollatzResearch.WordTrace tailWord_2388533 prefixEnd_2388533 272547886250135241633965 := by
  unfold tailWord_2388533
  simp only [CollatzResearch.WordTrace]
  refine ⟨87116955455760344804626253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58077970303840229869750835 87116955455760344804626253)
  ·
    refine ⟨32668858295910129301734845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 87116955455760344804626253 32668858295910129301734845)
    ·
      refine ⟨12250821860966298488150567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32668858295910129301734845 12250821860966298488150567)
      ·
        refine ⟨18376232791449447732225851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12250821860966298488150567 18376232791449447732225851)
        ·
          refine ⟨27564349187174171598338777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18376232791449447732225851 27564349187174171598338777)
          ·
            refine ⟨20673261890380628698754083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 27564349187174171598338777 20673261890380628698754083)
            ·
              refine ⟨31009892835570943048131125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20673261890380628698754083 31009892835570943048131125)
              ·
                refine ⟨2907177453334775910762293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31009892835570943048131125 2907177453334775910762293)
                ·
                  refine ⟨272547886250135241633965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2907177453334775910762293 272547886250135241633965)
                  ·
                    rfl

theorem cell22_2388533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 5, 5].length) (baseStart_2388533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388533 prefixEnd_2388533 := by exact prefixLift 2388533
  have htrace : WordTrace (prefixWord ++ tailWord_2388533) baseStart_2388533 baseEnd_2388533 := by
    simpa [prefixWord, tailWord_2388533, baseEnd_2388533] using wordTrace_append hprefix tailTrace_2388533
  have hstable : (prefixWord ++ tailWord_2388533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388533).length < 2 ^ (prefixWord ++ tailWord_2388533).sum := by decide
  have hdescent : baseEnd_2388533 < baseStart_2388533 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388608 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 1, 6]
def baseStart_2388608 : Nat := 118140960795 + 2388608 * 2 ^ 59
def prefixEnd_2388608 : Nat := 4983230072969 + 3 ^ 40 * 2388608 * 2
def baseEnd_2388608 : Nat := 817669332783130529276665

theorem tailTrace_2388608 : CollatzResearch.WordTrace tailWord_2388608 prefixEnd_2388608 817669332783130529276665 := by
  unfold tailWord_2388608
  simp only [CollatzResearch.WordTrace]
  refine ⟨43559845465244316306803239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58079793953659088409070985 43559845465244316306803239)
  ·
    refine ⟨65339768197866474460204859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43559845465244316306803239 65339768197866474460204859)
    ·
      refine ⟨98009652296799711690307289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65339768197866474460204859 98009652296799711690307289)
      ·
        refine ⟨73507239222599783767730467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 98009652296799711690307289 73507239222599783767730467)
        ·
          refine ⟨110260858833899675651595701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 73507239222599783767730467 110260858833899675651595701)
          ·
            refine ⟨10336955515678094592337097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 110260858833899675651595701 10336955515678094592337097)
            ·
              refine ⟨7752716636758570944252823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10336955515678094592337097 7752716636758570944252823)
              ·
                refine ⟨11629074955137856416379235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7752716636758570944252823 11629074955137856416379235)
                ·
                  refine ⟨17443612432706784624568853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11629074955137856416379235 17443612432706784624568853)
                  ·
                    refine ⟨817669332783130529276665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17443612432706784624568853 817669332783130529276665)
                    ·
                      rfl

theorem cell22_2388608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 1, 6].length) (baseStart_2388608 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388608 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388608 prefixEnd_2388608 := by exact prefixLift 2388608
  have htrace : WordTrace (prefixWord ++ tailWord_2388608) baseStart_2388608 baseEnd_2388608 := by
    simpa [prefixWord, tailWord_2388608, baseEnd_2388608] using wordTrace_append hprefix tailTrace_2388608
  have hstable : (prefixWord ++ tailWord_2388608).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388608).length < 2 ^ (prefixWord ++ tailWord_2388608).sum := by decide
  have hdescent : baseEnd_2388608 < baseStart_2388608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388612 : List Nat := [2, 3, 2, 1, 3, 1, 3, 3, 4]
def baseStart_2388612 : Nat := 118140960795 + 2388612 * 2 ^ 59
def prefixEnd_2388612 : Nat := 4983230072969 + 3 ^ 40 * 2388612 * 2
def baseEnd_2388612 : Nat := 272556900688291950725551

theorem tailTrace_2388612 : CollatzResearch.WordTrace tailWord_2388612 prefixEnd_2388612 272556900688291950725551 := by
  unfold tailWord_2388612
  simp only [CollatzResearch.WordTrace]
  refine ⟨43559918411237070648376045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58079891214982760864501393 43559918411237070648376045)
  ·
    refine ⟨16334969404213901493141017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43559918411237070648376045 16334969404213901493141017)
    ·
      refine ⟨12251227053160426119855763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16334969404213901493141017 12251227053160426119855763)
      ·
        refine ⟨18376840579740639179783645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12251227053160426119855763 18376840579740639179783645)
        ·
          refine ⟨6891315217402739692418867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18376840579740639179783645 6891315217402739692418867)
          ·
            refine ⟨10336972826104109538628301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6891315217402739692418867 10336972826104109538628301)
            ·
              refine ⟨3876364809789041076985613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10336972826104109538628301 3876364809789041076985613)
              ·
                refine ⟨1453636803670890403869605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3876364809789041076985613 1453636803670890403869605)
                ·
                  refine ⟨272556900688291950725551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1453636803670890403869605 272556900688291950725551)
                  ·
                    rfl

theorem cell22_2388612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_2388612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388612 prefixEnd_2388612 := by exact prefixLift 2388612
  have htrace : WordTrace (prefixWord ++ tailWord_2388612) baseStart_2388612 baseEnd_2388612 := by
    simpa [prefixWord, tailWord_2388612, baseEnd_2388612] using wordTrace_append hprefix tailTrace_2388612
  have hstable : (prefixWord ++ tailWord_2388612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388612).length < 2 ^ (prefixWord ++ tailWord_2388612).sum := by decide
  have hdescent : baseEnd_2388612 < baseStart_2388612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388640 : List Nat := [2, 1, 1, 4, 4, 1, 2, 7]
def baseStart_2388640 : Nat := 118140960795 + 2388640 * 2 ^ 59
def prefixEnd_2388640 : Nat := 4983230072969 + 3 ^ 40 * 2388640 * 2
def baseEnd_2388640 : Nat := 90853365226343679164063

theorem tailTrace_2388640 : CollatzResearch.WordTrace tailWord_2388640 prefixEnd_2388640 90853365226343679164063 := by
  unfold tailWord_2388640
  simp only [CollatzResearch.WordTrace]
  refine ⟨43560429033186351039385687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58080572044248468052514249 43560429033186351039385687)
  ·
    refine ⟨65340643549779526559078531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43560429033186351039385687 65340643549779526559078531)
    ·
      refine ⟨98010965324669289838617797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65340643549779526559078531 98010965324669289838617797)
      ·
        refine ⟨18377055998375491844740837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 98010965324669289838617797 18377055998375491844740837)
        ·
          refine ⟨3445697999695404720888907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 18377055998375491844740837 3445697999695404720888907)
          ·
            refine ⟨5168546999543107081333361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445697999695404720888907 5168546999543107081333361)
            ·
              refine ⟨3876410249657330311000021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5168546999543107081333361 3876410249657330311000021)
              ·
                refine ⟨90853365226343679164063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3876410249657330311000021 90853365226343679164063)
                ·
                  rfl

theorem cell22_2388640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 7].length) (baseStart_2388640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388640 prefixEnd_2388640 := by exact prefixLift 2388640
  have htrace : WordTrace (prefixWord ++ tailWord_2388640) baseStart_2388640 baseEnd_2388640 := by
    simpa [prefixWord, tailWord_2388640, baseEnd_2388640] using wordTrace_append hprefix tailTrace_2388640
  have hstable : (prefixWord ++ tailWord_2388640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388640).length < 2 ^ (prefixWord ++ tailWord_2388640).sum := by decide
  have hdescent : baseEnd_2388640 < baseStart_2388640 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388678 : List Nat := [6, 1, 2, 1, 2, 1, 2, 2, 2, 3]
def baseStart_2388678 : Nat := 118140960795 + 2388678 * 2 ^ 59
def prefixEnd_2388678 : Nat := 4983230072969 + 3 ^ 40 * 2388678 * 2
def baseEnd_2388678 : Nat := 817693295213673680026451

theorem tailTrace_2388678 : CollatzResearch.WordTrace tailWord_2388678 prefixEnd_2388678 817693295213673680026451 := by
  unfold tailWord_2388678
  simp only [CollatzResearch.WordTrace]
  refine ⟨2722570126257344830270459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 58081496026823356379103125 2722570126257344830270459)
  ·
    refine ⟨4083855189386017245405689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2722570126257344830270459 4083855189386017245405689)
    ·
      refine ⟨3062891392039512934054267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4083855189386017245405689 3062891392039512934054267)
      ·
        refine ⟨4594337088059269401081401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3062891392039512934054267 4594337088059269401081401)
        ·
          refine ⟨3445752816044452050811051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4594337088059269401081401 3445752816044452050811051)
          ·
            refine ⟨5168629224066678076216577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3445752816044452050811051 5168629224066678076216577)
            ·
              refine ⟨3876471918050008557162433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5168629224066678076216577 3876471918050008557162433)
              ·
                refine ⟨2907353938537506417871825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3876471918050008557162433 2907353938537506417871825)
                ·
                  refine ⟨2180515453903129813403869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2907353938537506417871825 2180515453903129813403869)
                  ·
                    refine ⟨817693295213673680026451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2180515453903129813403869 817693295213673680026451)
                    ·
                      rfl

theorem cell22_2388678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_2388678 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388678 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388678 prefixEnd_2388678 := by exact prefixLift 2388678
  have htrace : WordTrace (prefixWord ++ tailWord_2388678) baseStart_2388678 baseEnd_2388678 := by
    simpa [prefixWord, tailWord_2388678, baseEnd_2388678] using wordTrace_append hprefix tailTrace_2388678
  have hstable : (prefixWord ++ tailWord_2388678).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388678).length < 2 ^ (prefixWord ++ tailWord_2388678).sum := by decide
  have hdescent : baseEnd_2388678 < baseStart_2388678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388713 : List Nat := [1, 2, 1, 1, 1, 2, 5, 1, 8]
def baseStart_2388713 : Nat := 118140960795 + 2388713 * 2 ^ 59
def prefixEnd_2388713 : Nat := 4983230072969 + 3 ^ 40 * 2388713 * 2
def baseEnd_2388713 : Nat := 272568425476315085133781

theorem tailTrace_2388713 : CollatzResearch.WordTrace tailWord_2388713 prefixEnd_2388713 272568425476315085133781 := by
  unfold tailWord_2388713
  simp only [CollatzResearch.WordTrace]
  refine ⟨87123520595108235546178793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58082347063405490364119195 87123520595108235546178793)
  ·
    refine ⟨65342640446331176659634095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87123520595108235546178793 65342640446331176659634095)
    ·
      refine ⟨98013960669496764989451143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65342640446331176659634095 98013960669496764989451143)
      ·
        refine ⟨147020941004245147484176715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98013960669496764989451143 147020941004245147484176715)
        ·
          refine ⟨220531411506367721226265073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147020941004245147484176715 220531411506367721226265073)
          ·
            refine ⟨165398558629775790919698805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 220531411506367721226265073 165398558629775790919698805)
            ·
              refine ⟨15506114871541480398721763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 165398558629775790919698805 15506114871541480398721763)
              ·
                refine ⟨23259172307312220598082645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15506114871541480398721763 23259172307312220598082645)
                ·
                  refine ⟨272568425476315085133781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23259172307312220598082645 272568425476315085133781)
                  ·
                    rfl

theorem cell22_2388713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 1, 8].length) (baseStart_2388713 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388713 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388713 prefixEnd_2388713 := by exact prefixLift 2388713
  have htrace : WordTrace (prefixWord ++ tailWord_2388713) baseStart_2388713 baseEnd_2388713 := by
    simpa [prefixWord, tailWord_2388713, baseEnd_2388713] using wordTrace_append hprefix tailTrace_2388713
  have hstable : (prefixWord ++ tailWord_2388713).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388713).length < 2 ^ (prefixWord ++ tailWord_2388713).sum := by decide
  have hdescent : baseEnd_2388713 < baseStart_2388713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388715 : List Nat := [1, 1, 1, 1, 2, 4, 1, 6, 1, 4]
def baseStart_2388715 : Nat := 118140960795 + 2388715 * 2 ^ 59
def prefixEnd_2388715 : Nat := 4983230072969 + 3 ^ 40 * 2388715 * 2
def baseEnd_2388715 : Nat := 817705961069817916851337

theorem tailTrace_2388715 : CollatzResearch.WordTrace tailWord_2388715 prefixEnd_2388715 817705961069817916851337 := by
  unfold tailWord_2388715
  simp only [CollatzResearch.WordTrace]
  refine ⟨87123593541100989887751599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58082395694067326591834399 87123593541100989887751599)
  ·
    refine ⟨130685390311651484831627399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87123593541100989887751599 130685390311651484831627399)
    ·
      refine ⟨196028085467477227247441099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130685390311651484831627399 196028085467477227247441099)
      ·
        refine ⟨294042128201215840871161649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 196028085467477227247441099 294042128201215840871161649)
        ·
          refine ⟨220531596150911880653371237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 294042128201215840871161649 220531596150911880653371237)
          ·
            refine ⟨41349674278295977622507107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 220531596150911880653371237 41349674278295977622507107)
            ·
              refine ⟨62024511417443966433760661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41349674278295977622507107 62024511417443966433760661)
              ·
                refine ⟨2907398972692685926582531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 62024511417443966433760661 2907398972692685926582531)
                ·
                  refine ⟨4361098459039028889873797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907398972692685926582531 4361098459039028889873797)
                  ·
                    refine ⟨817705961069817916851337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4361098459039028889873797 817705961069817916851337)
                    ·
                      rfl

theorem cell22_2388715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 4].length) (baseStart_2388715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388715 prefixEnd_2388715 := by exact prefixLift 2388715
  have htrace : WordTrace (prefixWord ++ tailWord_2388715) baseStart_2388715 baseEnd_2388715 := by
    simpa [prefixWord, tailWord_2388715, baseEnd_2388715] using wordTrace_append hprefix tailTrace_2388715
  have hstable : (prefixWord ++ tailWord_2388715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388715).length < 2 ^ (prefixWord ++ tailWord_2388715).sum := by decide
  have hdescent : baseEnd_2388715 < baseStart_2388715 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388732 : List Nat := [2, 2, 2, 1, 3, 3, 1, 3, 1, 4]
def baseStart_2388732 : Nat := 118140960795 + 2388732 * 2 ^ 59
def prefixEnd_2388732 : Nat := 4983230072969 + 3 ^ 40 * 2388732 * 2
def baseEnd_2388732 : Nat := 817711780517235539176285

theorem tailTrace_2388732 : CollatzResearch.WordTrace tailWord_2388732 prefixEnd_2388732 817711780517235539176285 := by
  unfold tailWord_2388732
  simp only [CollatzResearch.WordTrace]
  refine ⟨43562106791019700895560225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58082809054692934527413633 43562106791019700895560225)
  ·
    refine ⟨32671580093264775671670169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43562106791019700895560225 32671580093264775671670169)
    ·
      refine ⟨24503685069948581753752627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32671580093264775671670169 24503685069948581753752627)
      ·
        refine ⟨36755527604922872630628941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24503685069948581753752627 36755527604922872630628941)
        ·
          refine ⟨13783322851846077236485853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 36755527604922872630628941 13783322851846077236485853)
          ·
            refine ⟨5168746069442278963682195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13783322851846077236485853 5168746069442278963682195)
            ·
              refine ⟨7753119104163418445523293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5168746069442278963682195 7753119104163418445523293)
              ·
                refine ⟨2907419664061281917071235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7753119104163418445523293 2907419664061281917071235)
                ·
                  refine ⟨4361129496091922875606853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907419664061281917071235 4361129496091922875606853)
                  ·
                    refine ⟨817711780517235539176285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4361129496091922875606853 817711780517235539176285)
                    ·
                      rfl

theorem cell22_2388732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_2388732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388732 prefixEnd_2388732 := by exact prefixLift 2388732
  have htrace : WordTrace (prefixWord ++ tailWord_2388732) baseStart_2388732 baseEnd_2388732 := by
    simpa [prefixWord, tailWord_2388732, baseEnd_2388732] using wordTrace_append hprefix tailTrace_2388732
  have hstable : (prefixWord ++ tailWord_2388732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388732).length < 2 ^ (prefixWord ++ tailWord_2388732).sum := by decide
  have hdescent : baseEnd_2388732 < baseStart_2388732 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388854 : List Nat := [5, 1, 1, 3, 1, 1, 1, 4, 5]
def baseStart_2388854 : Nat := 118140960795 + 2388854 * 2 ^ 59
def prefixEnd_2388854 : Nat := 4983230072969 + 3 ^ 40 * 2388854 * 2
def baseEnd_2388854 : Nat := 272584514536822629208637

theorem tailTrace_2388854 : CollatzResearch.WordTrace tailWord_2388854 prefixEnd_2388854 272584514536822629208637 := by
  unfold tailWord_2388854
  simp only [CollatzResearch.WordTrace]
  refine ⟨5445541455474838539191351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58085775525064944418041077 5445541455474838539191351)
  ·
    refine ⟨8168312183212257808787027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5445541455474838539191351 8168312183212257808787027)
    ·
      refine ⟨12252468274818386713180541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8168312183212257808787027 12252468274818386713180541)
      ·
        refine ⟨4594675603056895017442703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12252468274818386713180541 4594675603056895017442703)
        ·
          refine ⟨6892013404585342526164055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4594675603056895017442703 6892013404585342526164055)
          ·
            refine ⟨10338020106878013789246083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6892013404585342526164055 10338020106878013789246083)
            ·
              refine ⟨15507030160317020683869125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10338020106878013789246083 15507030160317020683869125)
              ·
                refine ⟨2907568155059441378225461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15507030160317020683869125 2907568155059441378225461)
                ·
                  refine ⟨272584514536822629208637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2907568155059441378225461 272584514536822629208637)
                  ·
                    rfl

theorem cell22_2388854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_2388854 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388854 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388854 prefixEnd_2388854 := by exact prefixLift 2388854
  have htrace : WordTrace (prefixWord ++ tailWord_2388854) baseStart_2388854 baseEnd_2388854 := by
    simpa [prefixWord, tailWord_2388854, baseEnd_2388854] using wordTrace_append hprefix tailTrace_2388854
  have hstable : (prefixWord ++ tailWord_2388854).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388854).length < 2 ^ (prefixWord ++ tailWord_2388854).sum := by decide
  have hdescent : baseEnd_2388854 < baseStart_2388854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388884 : List Nat := [2, 4, 2, 1, 1, 1, 2, 4, 1, 4]
def baseStart_2388884 : Nat := 118140960795 + 2388884 * 2 ^ 59
def prefixEnd_2388884 : Nat := 4983230072969 + 3 ^ 40 * 2388884 * 2
def baseEnd_2388884 : Nat := 817763813223557809375819

theorem tailTrace_2388884 : CollatzResearch.WordTrace tailWord_2388884 prefixEnd_2388884 817763813223557809375819 := by
  unfold tailWord_2388884
  simp only [CollatzResearch.WordTrace]
  refine ⟨43564878738744365875326853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58086504984992487833769137 43564878738744365875326853)
  ·
    refine ⟨8168414763514568601623785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 43564878738744365875326853 8168414763514568601623785)
    ·
      refine ⟨6126311072635926451217839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8168414763514568601623785 6126311072635926451217839)
      ·
        refine ⟨9189466608953889676826759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6126311072635926451217839 9189466608953889676826759)
        ·
          refine ⟨13784199913430834515240139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9189466608953889676826759 13784199913430834515240139)
          ·
            refine ⟨20676299870146251772860209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13784199913430834515240139 20676299870146251772860209)
            ·
              refine ⟨15507224902609688829645157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20676299870146251772860209 15507224902609688829645157)
              ·
                refine ⟨2907604669239316655558467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15507224902609688829645157 2907604669239316655558467)
                ·
                  refine ⟨4361407003858974983337701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907604669239316655558467 4361407003858974983337701)
                  ·
                    refine ⟨817763813223557809375819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4361407003858974983337701 817763813223557809375819)
                    ·
                      rfl

theorem cell22_2388884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_2388884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388884 prefixEnd_2388884 := by exact prefixLift 2388884
  have htrace : WordTrace (prefixWord ++ tailWord_2388884) baseStart_2388884 baseEnd_2388884 := by
    simpa [prefixWord, tailWord_2388884, baseEnd_2388884] using wordTrace_append hprefix tailTrace_2388884
  have hstable : (prefixWord ++ tailWord_2388884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388884).length < 2 ^ (prefixWord ++ tailWord_2388884).sum := by decide
  have hdescent : baseEnd_2388884 < baseStart_2388884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2388916 : List Nat := [2, 5, 2, 1, 1, 2, 2, 1, 6]
def baseStart_2388916 : Nat := 118140960795 + 2388916 * 2 ^ 59
def prefixEnd_2388916 : Nat := 4983230072969 + 3 ^ 40 * 2388916 * 2
def baseEnd_2388916 : Nat := 272591589159173464191907

theorem tailTrace_2388916 : CollatzResearch.WordTrace tailWord_2388916 prefixEnd_2388916 272591589159173464191907 := by
  unfold tailWord_2388916
  simp only [CollatzResearch.WordTrace]
  refine ⟨43565462306686400607909301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58087283075581867477212401 43565462306686400607909301)
  ·
    refine ⟨4084262091251850056991497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 43565462306686400607909301 4084262091251850056991497)
    ·
      refine ⟨3063196568438887542743623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4084262091251850056991497 3063196568438887542743623)
      ·
        refine ⟨4594794852658331314115435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063196568438887542743623 4594794852658331314115435)
        ·
          refine ⟨6892192278987496971173153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4594794852658331314115435 6892192278987496971173153)
          ·
            refine ⟨5169144209240622728379865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6892192278987496971173153 5169144209240622728379865)
            ·
              refine ⟨3876858156930467046284899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5169144209240622728379865 3876858156930467046284899)
              ·
                refine ⟨5815287235395700569427349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3876858156930467046284899 5815287235395700569427349)
                ·
                  refine ⟨272591589159173464191907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5815287235395700569427349 272591589159173464191907)
                  ·
                    rfl

theorem cell22_2388916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_2388916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2388916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2388916 prefixEnd_2388916 := by exact prefixLift 2388916
  have htrace : WordTrace (prefixWord ++ tailWord_2388916) baseStart_2388916 baseEnd_2388916 := by
    simpa [prefixWord, tailWord_2388916, baseEnd_2388916] using wordTrace_append hprefix tailTrace_2388916
  have hstable : (prefixWord ++ tailWord_2388916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2388916).length < 2 ^ (prefixWord ++ tailWord_2388916).sum := by decide
  have hdescent : baseEnd_2388916 < baseStart_2388916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2388916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389047 : List Nat := [1, 1, 3, 1, 2, 2, 1, 4, 1, 6]
def baseStart_2389047 : Nat := 118140960795 + 2389047 * 2 ^ 59
def prefixEnd_2389047 : Nat := 4983230072969 + 3 ^ 40 * 2389047 * 2
def baseEnd_2389047 : Nat := 817819611454679717550319

theorem tailTrace_2389047 : CollatzResearch.WordTrace tailWord_2389047 prefixEnd_2389047 817819611454679717550319 := by
  unfold tailWord_2389047
  simp only [CollatzResearch.WordTrace]
  refine ⟨87135702575898210588837395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58090468383932140392558263 87135702575898210588837395)
  ·
    refine ⟨130703553863847315883256093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87135702575898210588837395 130703553863847315883256093)
    ·
      refine ⟨49013832698942743456221035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 130703553863847315883256093 49013832698942743456221035)
      ·
        refine ⟨73520749048414115184331553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 49013832698942743456221035 73520749048414115184331553)
        ·
          refine ⟨55140561786310586388248665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 73520749048414115184331553 55140561786310586388248665)
          ·
            refine ⟨41355421339732939791186499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55140561786310586388248665 41355421339732939791186499)
            ·
              refine ⟨62033132009599409686779749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 41355421339732939791186499 62033132009599409686779749)
              ·
                refine ⟨11631212251799889316271203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 62033132009599409686779749 11631212251799889316271203)
                ·
                  refine ⟨17446818377699833974406805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11631212251799889316271203 17446818377699833974406805)
                  ·
                    refine ⟨817819611454679717550319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17446818377699833974406805 817819611454679717550319)
                    ·
                      rfl

theorem cell22_2389047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 6].length) (baseStart_2389047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389047 prefixEnd_2389047 := by exact prefixLift 2389047
  have htrace : WordTrace (prefixWord ++ tailWord_2389047) baseStart_2389047 baseEnd_2389047 := by
    simpa [prefixWord, tailWord_2389047, baseEnd_2389047] using wordTrace_append hprefix tailTrace_2389047
  have hstable : (prefixWord ++ tailWord_2389047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389047).length < 2 ^ (prefixWord ++ tailWord_2389047).sum := by decide
  have hdescent : baseEnd_2389047 < baseStart_2389047 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389049 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 1, 5]
def baseStart_2389049 : Nat := 118140960795 + 2389049 * 2 ^ 59
def prefixEnd_2389049 : Nat := 4983230072969 + 3 ^ 40 * 2389049 * 2
def baseEnd_2389049 : Nat := 817820296095552379000313

theorem tailTrace_2389049 : CollatzResearch.WordTrace tailWord_2389049 prefixEnd_2389049 817820296095552379000313 := by
  unfold tailWord_2389049
  simp only [CollatzResearch.WordTrace]
  refine ⟨87135775521890964930410201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58090517014593976620273467 87135775521890964930410201)
  ·
    refine ⟨65351831641418223697807651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87135775521890964930410201 65351831641418223697807651)
    ·
      refine ⟨98027747462127335546711477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65351831641418223697807651 98027747462127335546711477)
      ·
        refine ⟨9190101324574437707504201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 98027747462127335546711477 9190101324574437707504201)
        ·
          refine ⟨6892575993430828280628151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9190101324574437707504201 6892575993430828280628151)
          ·
            refine ⟨10338863990146242420942227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6892575993430828280628151 10338863990146242420942227)
            ·
              refine ⟨15508295985219363631413341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10338863990146242420942227 15508295985219363631413341)
              ·
                refine ⟨5815610994457261361780003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15508295985219363631413341 5815610994457261361780003)
                ·
                  refine ⟨8723416491685892042670005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5815610994457261361780003 8723416491685892042670005)
                  ·
                    refine ⟨817820296095552379000313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8723416491685892042670005 817820296095552379000313)
                    ·
                      rfl

theorem cell22_2389049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 5].length) (baseStart_2389049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389049 prefixEnd_2389049 := by exact prefixLift 2389049
  have htrace : WordTrace (prefixWord ++ tailWord_2389049) baseStart_2389049 baseEnd_2389049 := by
    simpa [prefixWord, tailWord_2389049, baseEnd_2389049] using wordTrace_append hprefix tailTrace_2389049
  have hstable : (prefixWord ++ tailWord_2389049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389049).length < 2 ^ (prefixWord ++ tailWord_2389049).sum := by decide
  have hdescent : baseEnd_2389049 < baseStart_2389049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389113 : List Nat := [1, 2, 1, 3, 6, 1, 2, 6]
def baseStart_2389113 : Nat := 118140960795 + 2389113 * 2 ^ 59
def prefixEnd_2389113 : Nat := 4983230072969 + 3 ^ 40 * 2389113 * 2
def baseEnd_2389113 : Nat := 90871356067053060600013

theorem tailTrace_2389113 : CollatzResearch.WordTrace tailWord_2389113 prefixEnd_2389113 90871356067053060600013 := by
  unfold tailWord_2389113
  simp only [CollatzResearch.WordTrace]
  refine ⟨87138109793659103860739993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58092073195772735907159995 87138109793659103860739993)
  ·
    refine ⟨65353582345244327895554995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87138109793659103860739993 65353582345244327895554995)
    ·
      refine ⟨98030373517866491843332493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65353582345244327895554995 98030373517866491843332493)
      ·
        refine ⟨36761390069199934441249685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 98030373517866491843332493 36761390069199934441249685)
        ·
          refine ⟨1723190159493746926933579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 36761390069199934441249685 1723190159493746926933579)
          ·
            refine ⟨2584785239240620390400369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1723190159493746926933579 2584785239240620390400369)
            ·
              refine ⟨1938588929430465292800277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2584785239240620390400369 1938588929430465292800277)
              ·
                refine ⟨90871356067053060600013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1938588929430465292800277 90871356067053060600013)
                ·
                  rfl

theorem cell22_2389113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 6].length) (baseStart_2389113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389113 prefixEnd_2389113 := by exact prefixLift 2389113
  have htrace : WordTrace (prefixWord ++ tailWord_2389113) baseStart_2389113 baseEnd_2389113 := by
    simpa [prefixWord, tailWord_2389113, baseEnd_2389113] using wordTrace_append hprefix tailTrace_2389113
  have hstable : (prefixWord ++ tailWord_2389113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389113).length < 2 ^ (prefixWord ++ tailWord_2389113).sum := by decide
  have hdescent : baseEnd_2389113 < baseStart_2389113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389124 : List Nat := [2, 3, 2, 1, 2, 2, 1, 2, 7]
def baseStart_2389124 : Nat := 118140960795 + 2389124 * 2 ^ 59
def prefixEnd_2389124 : Nat := 4983230072969 + 3 ^ 40 * 2389124 * 2
def baseEnd_2389124 : Nat := 272615323376092394458361

theorem tailTrace_2389124 : CollatzResearch.WordTrace tailWord_2389124 prefixEnd_2389124 272615323376092394458361 := by
  unfold tailWord_2389124
  simp only [CollatzResearch.WordTrace]
  refine ⟨43569255498309626369695213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58092340664412835159593617 43569255498309626369695213)
  ·
    refine ⟨16338470811866109888635705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 43569255498309626369695213 16338470811866109888635705)
    ·
      refine ⟨12253853108899582416476779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16338470811866109888635705 12253853108899582416476779)
      ·
        refine ⟨18380779663349373624715169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12253853108899582416476779 18380779663349373624715169)
        ·
          refine ⟨13785584747512030218536377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18380779663349373624715169 13785584747512030218536377)
          ·
            refine ⟨10339188560634022663902283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13785584747512030218536377 10339188560634022663902283)
            ·
              refine ⟨15508782840951033995853425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10339188560634022663902283 15508782840951033995853425)
              ·
                refine ⟨11631587130713275496890069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15508782840951033995853425 11631587130713275496890069)
                ·
                  refine ⟨272615323376092394458361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11631587130713275496890069 272615323376092394458361)
                  ·
                    rfl

theorem cell22_2389124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_2389124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389124 prefixEnd_2389124 := by exact prefixLift 2389124
  have htrace : WordTrace (prefixWord ++ tailWord_2389124) baseStart_2389124 baseEnd_2389124 := by
    simpa [prefixWord, tailWord_2389124, baseEnd_2389124] using wordTrace_append hprefix tailTrace_2389124
  have hstable : (prefixWord ++ tailWord_2389124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389124).length < 2 ^ (prefixWord ++ tailWord_2389124).sum := by decide
  have hdescent : baseEnd_2389124 < baseStart_2389124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389171 : List Nat := [1, 1, 1, 2, 3, 2, 5, 2, 1, 4]
def baseStart_2389171 : Nat := 118140960795 + 2389171 * 2 ^ 59
def prefixEnd_2389171 : Nat := 4983230072969 + 3 ^ 40 * 2389171 * 2
def baseEnd_2389171 : Nat := 817862059188784727449939

theorem tailTrace_2389171 : CollatzResearch.WordTrace tailWord_2389171 prefixEnd_2389171 817862059188784727449939 := by
  unfold tailWord_2389171
  simp only [CollatzResearch.WordTrace]
  refine ⟨87140225227448979766351367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58093483484965986510900911 87140225227448979766351367)
  ·
    refine ⟨130710337841173469649527051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87140225227448979766351367 130710337841173469649527051)
    ·
      refine ⟨196065506761760204474290577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130710337841173469649527051 196065506761760204474290577)
      ·
        refine ⟨147049130071320153355717933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 196065506761760204474290577 147049130071320153355717933)
        ·
          refine ⟨55143423776745057508394225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 147049130071320153355717933 55143423776745057508394225)
          ·
            refine ⟨41357567832558793131295669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 55143423776745057508394225 41357567832558793131295669)
            ·
              refine ⟨3877271984302386856058969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41357567832558793131295669 3877271984302386856058969)
              ·
                refine ⟨2907953988226790142044227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3877271984302386856058969 2907953988226790142044227)
                ·
                  refine ⟨4361930982340185213066341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2907953988226790142044227 4361930982340185213066341)
                  ·
                    refine ⟨817862059188784727449939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4361930982340185213066341 817862059188784727449939)
                    ·
                      rfl

theorem cell22_2389171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 4].length) (baseStart_2389171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389171 prefixEnd_2389171 := by exact prefixLift 2389171
  have htrace : WordTrace (prefixWord ++ tailWord_2389171) baseStart_2389171 baseEnd_2389171 := by
    simpa [prefixWord, tailWord_2389171, baseEnd_2389171] using wordTrace_append hprefix tailTrace_2389171
  have hstable : (prefixWord ++ tailWord_2389171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389171).length < 2 ^ (prefixWord ++ tailWord_2389171).sum := by decide
  have hdescent : baseEnd_2389171 < baseStart_2389171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389199 : List Nat := [1, 1, 2, 1, 1, 3, 2, 3, 4, 4]
def baseStart_2389199 : Nat := 118140960795 + 2389199 * 2 ^ 59
def prefixEnd_2389199 : Nat := 4983230072969 + 3 ^ 40 * 2389199 * 2
def baseEnd_2389199 : Nat := 817871644161001987749853

theorem tailTrace_2389199 : CollatzResearch.WordTrace tailWord_2389199 prefixEnd_2389199 817871644161001987749853 := by
  unfold tailWord_2389199
  simp only [CollatzResearch.WordTrace]
  refine ⟨87141246471347540548370651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58094164314231693698913767 87141246471347540548370651)
  ·
    refine ⟨130711869707021310822555977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87141246471347540548370651 130711869707021310822555977)
    ·
      refine ⟨98033902280265983116916983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 130711869707021310822555977 98033902280265983116916983)
      ·
        refine ⟨147050853420398974675375475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98033902280265983116916983 147050853420398974675375475)
        ·
          refine ⟨220576280130598462013063213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 147050853420398974675375475 220576280130598462013063213)
          ·
            refine ⟨82716105048974423254898705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 220576280130598462013063213 82716105048974423254898705)
            ·
              refine ⟨62037078786730817441174029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 82716105048974423254898705 62037078786730817441174029)
              ·
                refine ⟨23263904545024056540440261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 62037078786730817441174029 23263904545024056540440261)
                ·
                  refine ⟨4361982102192010601332549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23263904545024056540440261 4361982102192010601332549)
                  ·
                    refine ⟨817871644161001987749853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4361982102192010601332549 817871644161001987749853)
                    ·
                      rfl

theorem cell22_2389199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 3, 4, 4].length) (baseStart_2389199 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389199 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389199 prefixEnd_2389199 := by exact prefixLift 2389199
  have htrace : WordTrace (prefixWord ++ tailWord_2389199) baseStart_2389199 baseEnd_2389199 := by
    simpa [prefixWord, tailWord_2389199, baseEnd_2389199] using wordTrace_append hprefix tailTrace_2389199
  have hstable : (prefixWord ++ tailWord_2389199).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389199).length < 2 ^ (prefixWord ++ tailWord_2389199).sum := by decide
  have hdescent : baseEnd_2389199 < baseStart_2389199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389276 : List Nat := [2, 2, 3, 1, 1, 1, 2, 5, 5]
def baseStart_2389276 : Nat := 118140960795 + 2389276 * 2 ^ 59
def prefixEnd_2389276 : Nat := 4983230072969 + 3 ^ 40 * 2389276 * 2
def baseEnd_2389276 : Nat := 272632667611533151191539

theorem tailTrace_2389276 : CollatzResearch.WordTrace tailWord_2389276 prefixEnd_2389276 272632667611533151191539 := by
  unfold tailWord_2389276
  simp only [CollatzResearch.WordTrace]
  refine ⟨43572027446034291349461841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58096036594712388465949121 43572027446034291349461841)
  ·
    refine ⟨32679020584525718512096381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 43572027446034291349461841 32679020584525718512096381)
    ·
      refine ⟨12254632719197144442036143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 32679020584525718512096381 12254632719197144442036143)
      ·
        refine ⟨18381949078795716663054215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12254632719197144442036143 18381949078795716663054215)
        ·
          refine ⟨27572923618193574994581323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18381949078795716663054215 27572923618193574994581323)
          ·
            refine ⟨41359385427290362491871985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 27572923618193574994581323 41359385427290362491871985)
            ·
              refine ⟨31019539070467771868903989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 41359385427290362491871985 31019539070467771868903989)
              ·
                refine ⟨2908081787856353612709749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31019539070467771868903989 2908081787856353612709749)
                ·
                  refine ⟨272632667611533151191539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2908081787856353612709749 272632667611533151191539)
                  ·
                    rfl

theorem cell22_2389276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_2389276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389276 prefixEnd_2389276 := by exact prefixLift 2389276
  have htrace : WordTrace (prefixWord ++ tailWord_2389276) baseStart_2389276 baseEnd_2389276 := by
    simpa [prefixWord, tailWord_2389276, baseEnd_2389276] using wordTrace_append hprefix tailTrace_2389276
  have hstable : (prefixWord ++ tailWord_2389276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389276).length < 2 ^ (prefixWord ++ tailWord_2389276).sum := by decide
  have hdescent : baseEnd_2389276 < baseStart_2389276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389293 : List Nat := [1, 5, 3, 1, 1, 1, 1, 2, 7]
def baseStart_2389293 : Nat := 118140960795 + 2389293 * 2 ^ 59
def prefixEnd_2389293 : Nat := 4983230072969 + 3 ^ 40 * 2389293 * 2
def baseEnd_2389293 : Nat := 272634607427339025299855

theorem tailTrace_2389293 : CollatzResearch.WordTrace tailWord_2389293 prefixEnd_2389293 272634607427339025299855 := by
  unfold tailWord_2389293
  simp only [CollatzResearch.WordTrace]
  refine ⟨87144674933006994602292533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58096449955337996401528355 87144674933006994602292533)
  ·
    refine ⟨8169813274969405743964925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 87144674933006994602292533 8169813274969405743964925)
    ·
      refine ⟨3063679978113527153986847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8169813274969405743964925 3063679978113527153986847)
      ·
        refine ⟨4595519967170290730980271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3063679978113527153986847 4595519967170290730980271)
        ·
          refine ⟨6893279950755436096470407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595519967170290730980271 6893279950755436096470407)
          ·
            refine ⟨10339919926133154144705611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6893279950755436096470407 10339919926133154144705611)
            ·
              refine ⟨15509879889199731217058417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10339919926133154144705611 15509879889199731217058417)
              ·
                refine ⟨11632409916899798412793813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15509879889199731217058417 11632409916899798412793813)
                ·
                  refine ⟨272634607427339025299855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11632409916899798412793813 272634607427339025299855)
                  ·
                    rfl

theorem cell22_2389293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_2389293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389293 prefixEnd_2389293 := by exact prefixLift 2389293
  have htrace : WordTrace (prefixWord ++ tailWord_2389293) baseStart_2389293 baseEnd_2389293 := by
    simpa [prefixWord, tailWord_2389293, baseEnd_2389293] using wordTrace_append hprefix tailTrace_2389293
  have hstable : (prefixWord ++ tailWord_2389293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389293).length < 2 ^ (prefixWord ++ tailWord_2389293).sum := by decide
  have hdescent : baseEnd_2389293 < baseStart_2389293 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389297 : List Nat := [1, 2, 2, 3, 3, 3, 1, 3, 1, 3]
def baseStart_2389297 : Nat := 118140960795 + 2389297 * 2 ^ 59
def prefixEnd_2389297 : Nat := 4983230072969 + 3 ^ 40 * 2389297 * 2
def baseEnd_2389297 : Nat := 817905191563762398799553

theorem tailTrace_2389297 : CollatzResearch.WordTrace tailWord_2389297 prefixEnd_2389297 817905191563762398799553 := by
  unfold tailWord_2389297
  simp only [CollatzResearch.WordTrace]
  refine ⟨87144820824992503285438145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58096547216661668856958763 87144820824992503285438145)
  ·
    refine ⟨65358615618744377464078609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87144820824992503285438145 65358615618744377464078609)
    ·
      refine ⟨49018961714058283098058957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65358615618744377464078609 49018961714058283098058957)
      ·
        refine ⟨18382110642771856161772109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 49018961714058283098058957 18382110642771856161772109)
        ·
          refine ⟨6893291491039446060664541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18382110642771856161772109 6893291491039446060664541)
          ·
            refine ⟨2584984309139792272749203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6893291491039446060664541 2584984309139792272749203)
            ·
              refine ⟨3877476463709688409123805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2584984309139792272749203 3877476463709688409123805)
              ·
                refine ⟨1454053673891133153421427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3877476463709688409123805 1454053673891133153421427)
                ·
                  refine ⟨2181080510836699730132141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1454053673891133153421427 2181080510836699730132141)
                  ·
                    refine ⟨817905191563762398799553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2181080510836699730132141 817905191563762398799553)
                    ·
                      rfl

theorem cell22_2389297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 3, 1, 3].length) (baseStart_2389297 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389297 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389297 prefixEnd_2389297 := by exact prefixLift 2389297
  have htrace : WordTrace (prefixWord ++ tailWord_2389297) baseStart_2389297 baseEnd_2389297 := by
    simpa [prefixWord, tailWord_2389297, baseEnd_2389297] using wordTrace_append hprefix tailTrace_2389297
  have hstable : (prefixWord ++ tailWord_2389297).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389297).length < 2 ^ (prefixWord ++ tailWord_2389297).sum := by decide
  have hdescent : baseEnd_2389297 < baseStart_2389297 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389321 : List Nat := [1, 2, 1, 1, 2, 3, 5, 1, 6]
def baseStart_2389321 : Nat := 118140960795 + 2389321 * 2 ^ 59
def prefixEnd_2389321 : Nat := 4983230072969 + 3 ^ 40 * 2389321 * 2
def baseEnd_2389321 : Nat := 272637802418078112066493

theorem tailTrace_2389321 : CollatzResearch.WordTrace tailWord_2389321 prefixEnd_2389321 272637802418078112066493 := by
  unfold tailWord_2389321
  simp only [CollatzResearch.WordTrace]
  refine ⟨87145696176905555384311817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58097130784603703589541211 87145696176905555384311817)
  ·
    refine ⟨65359272132679166538233863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 87145696176905555384311817 65359272132679166538233863)
    ·
      refine ⟨98038908199018749807350795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 65359272132679166538233863 98038908199018749807350795)
      ·
        refine ⟨147058362298528124711026193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 98038908199018749807350795 147058362298528124711026193)
        ·
          refine ⟨110293771723896093533269645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 147058362298528124711026193 110293771723896093533269645)
          ·
            refine ⟨41360164396461035074976117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 110293771723896093533269645 41360164396461035074976117)
            ·
              refine ⟨3877515412168222038279011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 41360164396461035074976117 3877515412168222038279011)
              ·
                refine ⟨5816273118252333057418517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877515412168222038279011 5816273118252333057418517)
                ·
                  refine ⟨272637802418078112066493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5816273118252333057418517 272637802418078112066493)
                  ·
                    rfl

theorem cell22_2389321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 1, 6].length) (baseStart_2389321 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389321 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389321 prefixEnd_2389321 := by exact prefixLift 2389321
  have htrace : WordTrace (prefixWord ++ tailWord_2389321) baseStart_2389321 baseEnd_2389321 := by
    simpa [prefixWord, tailWord_2389321, baseEnd_2389321] using wordTrace_append hprefix tailTrace_2389321
  have hstable : (prefixWord ++ tailWord_2389321).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389321).length < 2 ^ (prefixWord ++ tailWord_2389321).sum := by decide
  have hdescent : baseEnd_2389321 < baseStart_2389321 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389336 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 1, 5]
def baseStart_2389336 : Nat := 118140960795 + 2389336 * 2 ^ 59
def prefixEnd_2389336 : Nat := 4983230072969 + 3 ^ 40 * 2389336 * 2
def baseEnd_2389336 : Nat := 817918542060779297074433

theorem tailTrace_2389336 : CollatzResearch.WordTrace tailWord_2389336 prefixEnd_2389336 817918542060779297074433 := by
  unfold tailWord_2389336
  simp only [CollatzResearch.WordTrace]
  refine ⟨43573121635925606473053931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58097495514567475297405241 43573121635925606473053931)
  ·
    refine ⟨65359682453888409709580897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43573121635925606473053931 65359682453888409709580897)
    ·
      refine ⟨49019761840416307282185673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65359682453888409709580897 49019761840416307282185673)
      ·
        refine ⟨36764821380312230461639255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 49019761840416307282185673 36764821380312230461639255)
        ·
          refine ⟨55147232070468345692458883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36764821380312230461639255 55147232070468345692458883)
          ·
            refine ⟨82720848105702518538688325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 55147232070468345692458883 82720848105702518538688325)
            ·
              refine ⟨15510159019819222226004061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 82720848105702518538688325 15510159019819222226004061)
              ·
                refine ⟨5816309632432208334751523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15510159019819222226004061 5816309632432208334751523)
                ·
                  refine ⟨8724464448648312502127285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5816309632432208334751523 8724464448648312502127285)
                  ·
                    refine ⟨817918542060779297074433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8724464448648312502127285 817918542060779297074433)
                    ·
                      rfl

theorem cell22_2389336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 1, 5].length) (baseStart_2389336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389336 prefixEnd_2389336 := by exact prefixLift 2389336
  have htrace : WordTrace (prefixWord ++ tailWord_2389336) baseStart_2389336 baseEnd_2389336 := by
    simpa [prefixWord, tailWord_2389336, baseEnd_2389336] using wordTrace_append hprefix tailTrace_2389336
  have hstable : (prefixWord ++ tailWord_2389336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389336).length < 2 ^ (prefixWord ++ tailWord_2389336).sum := by decide
  have hdescent : baseEnd_2389336 < baseStart_2389336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389366 : List Nat := [5, 1, 1, 15]
def baseStart_2389366 : Nat := 118140960795 + 2389366 * 2 ^ 59
def prefixEnd_2389366 : Nat := 4983230072969 + 3 ^ 40 * 2389366 * 2
def baseEnd_2389366 : Nat := 1121987395986103180829

theorem tailTrace_2389366 : CollatzResearch.WordTrace tailWord_2389366 prefixEnd_2389366 1121987395986103180829 := by
  unfold tailWord_2389366
  simp only [CollatzResearch.WordTrace]
  refine ⟨5446708591358908004356247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 58098224974495018713133301 5446708591358908004356247)
  ·
    refine ⟨8170062887038362006534371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5446708591358908004356247 8170062887038362006534371)
    ·
      refine ⟨12255094330557543009801557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8170062887038362006534371 12255094330557543009801557)
      ·
        refine ⟨1121987395986103180829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 12255094330557543009801557 1121987395986103180829)
        ·
          rfl

theorem cell22_2389366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 15].length) (baseStart_2389366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389366 prefixEnd_2389366 := by exact prefixLift 2389366
  have htrace : WordTrace (prefixWord ++ tailWord_2389366) baseStart_2389366 baseEnd_2389366 := by
    simpa [prefixWord, tailWord_2389366, baseEnd_2389366] using wordTrace_append hprefix tailTrace_2389366
  have hstable : (prefixWord ++ tailWord_2389366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389366).length < 2 ^ (prefixWord ++ tailWord_2389366).sum := by decide
  have hdescent : baseEnd_2389366 < baseStart_2389366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389383 : List Nat := [1, 1, 4, 2, 2, 4, 1, 7]
def baseStart_2389383 : Nat := 118140960795 + 2389383 * 2 ^ 59
def prefixEnd_2389383 : Nat := 4983230072969 + 3 ^ 40 * 2389383 * 2
def baseEnd_2389383 : Nat := 90881625680142982349921

theorem tailTrace_2389383 : CollatzResearch.WordTrace tailWord_2389383 prefixEnd_2389383 90881625680142982349921 := by
  unfold tailWord_2389383
  simp only [CollatzResearch.WordTrace]
  refine ⟨87147957502680939973068803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58098638335120626648712535 87147957502680939973068803)
  ·
    refine ⟨130721936254021409959603205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87147957502680939973068803 130721936254021409959603205)
    ·
      refine ⟨24510363047629014367425601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 130721936254021409959603205 24510363047629014367425601)
      ·
        refine ⟨18382772285721760775569201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 24510363047629014367425601 18382772285721760775569201)
        ·
          refine ⟨13787079214291320581676901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18382772285721760775569201 13787079214291320581676901)
          ·
            refine ⟨2585077352679622609064419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13787079214291320581676901 2585077352679622609064419)
            ·
              refine ⟨3877616029019433913596629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2585077352679622609064419 3877616029019433913596629)
              ·
                refine ⟨90881625680142982349921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3877616029019433913596629 90881625680142982349921)
                ·
                  rfl

theorem cell22_2389383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 7].length) (baseStart_2389383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389383 prefixEnd_2389383 := by exact prefixLift 2389383
  have htrace : WordTrace (prefixWord ++ tailWord_2389383) baseStart_2389383 baseEnd_2389383 := by
    simpa [prefixWord, tailWord_2389383, baseEnd_2389383] using wordTrace_append hprefix tailTrace_2389383
  have hstable : (prefixWord ++ tailWord_2389383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389383).length < 2 ^ (prefixWord ++ tailWord_2389383).sum := by decide
  have hdescent : baseEnd_2389383 < baseStart_2389383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389400 : List Nat := [2, 1, 2, 5, 2, 1, 3, 6]
def baseStart_2389400 : Nat := 118140960795 + 2389400 * 2 ^ 59
def prefixEnd_2389400 : Nat := 4983230072969 + 3 ^ 40 * 2389400 * 2
def baseEnd_2389400 : Nat := 90882272285411607052693

theorem tailTrace_2389400 : CollatzResearch.WordTrace tailWord_2389400 prefixEnd_2389400 90882272285411607052693 := by
  unfold tailWord_2389400
  simp only [CollatzResearch.WordTrace]
  refine ⟨43574288771809675938218827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 58099051695746234584291769 43574288771809675938218827)
  ·
    refine ⟨65361433157714513907328241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 43574288771809675938218827 65361433157714513907328241)
    ·
      refine ⟨49021074868285885430496181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 65361433157714513907328241 49021074868285885430496181)
      ·
        refine ⟨4595725768901801759109017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 49021074868285885430496181 4595725768901801759109017)
        ·
          refine ⟨3446794326676351319331763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4595725768901801759109017 3446794326676351319331763)
          ·
            refine ⟨5170191490014526978997645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3446794326676351319331763 5170191490014526978997645)
            ·
              refine ⟨1938821808755447617124117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5170191490014526978997645 1938821808755447617124117)
              ·
                refine ⟨90882272285411607052693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1938821808755447617124117 90882272285411607052693)
                ·
                  rfl

theorem cell22_2389400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 6].length) (baseStart_2389400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389400 prefixEnd_2389400 := by exact prefixLift 2389400
  have htrace : WordTrace (prefixWord ++ tailWord_2389400) baseStart_2389400 baseEnd_2389400 := by
    simpa [prefixWord, tailWord_2389400, baseEnd_2389400] using wordTrace_append hprefix tailTrace_2389400
  have hstable : (prefixWord ++ tailWord_2389400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389400).length < 2 ^ (prefixWord ++ tailWord_2389400).sum := by decide
  have hdescent : baseEnd_2389400 < baseStart_2389400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389411 : List Nat := [1, 1, 1, 4, 1, 3, 2, 2, 7]
def baseStart_2389411 : Nat := 118140960795 + 2389411 * 2 ^ 59
def prefixEnd_2389411 : Nat := 4983230072969 + 3 ^ 40 * 2389411 * 2
def baseEnd_2389411 : Nat := 272648072031168033816401

theorem tailTrace_2389411 : CollatzResearch.WordTrace tailWord_2389411 prefixEnd_2389411 272648072031168033816401 := by
  unfold tailWord_2389411
  simp only [CollatzResearch.WordTrace]
  refine ⟨87148978746579500755088087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58099319164386333836725391 87148978746579500755088087)
  ·
    refine ⟨130723468119869251132632131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87148978746579500755088087 130723468119869251132632131)
    ·
      refine ⟨196085202179803876698948197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130723468119869251132632131 196085202179803876698948197)
      ·
        refine ⟨36765975408713226881052787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 196085202179803876698948197 36765975408713226881052787)
        ·
          refine ⟨55148963113069840321579181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36765975408713226881052787 55148963113069840321579181)
          ·
            refine ⟨20680861167401190120592193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55148963113069840321579181 20680861167401190120592193)
            ·
              refine ⟨15510645875550892590444145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 20680861167401190120592193 15510645875550892590444145)
              ·
                refine ⟨11632984406663169442833109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15510645875550892590444145 11632984406663169442833109)
                ·
                  refine ⟨272648072031168033816401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11632984406663169442833109 272648072031168033816401)
                  ·
                    rfl

theorem cell22_2389411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 2, 7].length) (baseStart_2389411 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389411 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389411 prefixEnd_2389411 := by exact prefixLift 2389411
  have htrace : WordTrace (prefixWord ++ tailWord_2389411) baseStart_2389411 baseEnd_2389411 := by
    simpa [prefixWord, tailWord_2389411, baseEnd_2389411] using wordTrace_append hprefix tailTrace_2389411
  have hstable : (prefixWord ++ tailWord_2389411).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389411).length < 2 ^ (prefixWord ++ tailWord_2389411).sum := by decide
  have hdescent : baseEnd_2389411 < baseStart_2389411 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389475 : List Nat := [1, 1, 1, 6, 2, 1, 2, 3, 1, 4]
def baseStart_2389475 : Nat := 118140960795 + 2389475 * 2 ^ 59
def prefixEnd_2389475 : Nat := 4983230072969 + 3 ^ 40 * 2389475 * 2
def baseEnd_2389475 : Nat := 817966124601429267849007

theorem tailTrace_2389475 : CollatzResearch.WordTrace tailWord_2389475 prefixEnd_2389475 817966124601429267849007 := by
  unfold tailWord_2389475
  simp only [CollatzResearch.WordTrace]
  refine ⟨87151313018347639685417879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 58100875345565093123611919 87151313018347639685417879)
  ·
    refine ⟨130726969527521459528126819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 87151313018347639685417879 130726969527521459528126819)
    ·
      refine ⟨196090454291282189292190229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 130726969527521459528126819 196090454291282189292190229)
      ·
        refine ⟨9191740044903852623071417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 196090454291282189292190229 9191740044903852623071417)
        ·
          refine ⟨6893805033677889467303563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9191740044903852623071417 6893805033677889467303563)
          ·
            refine ⟨10340707550516834200955345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6893805033677889467303563 10340707550516834200955345)
            ·
              refine ⟨7755530662887625650716509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10340707550516834200955345 7755530662887625650716509)
              ·
                refine ⟨2908323998582859619018691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7755530662887625650716509 2908323998582859619018691)
                ·
                  refine ⟨4362485997874289428528037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2908323998582859619018691 4362485997874289428528037)
                  ·
                    refine ⟨817966124601429267849007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4362485997874289428528037 817966124601429267849007)
                    ·
                      rfl

theorem cell22_2389475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 4].length) (baseStart_2389475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389475 prefixEnd_2389475 := by exact prefixLift 2389475
  have htrace : WordTrace (prefixWord ++ tailWord_2389475) baseStart_2389475 baseEnd_2389475 := by
    simpa [prefixWord, tailWord_2389475, baseEnd_2389475] using wordTrace_append hprefix tailTrace_2389475
  have hstable : (prefixWord ++ tailWord_2389475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389475).length < 2 ^ (prefixWord ++ tailWord_2389475).sum := by decide
  have hdescent : baseEnd_2389475 < baseStart_2389475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389490 : List Nat := [3, 2, 1, 4, 1, 1, 3, 1, 6]
def baseStart_2389490 : Nat := 118140960795 + 2389490 * 2 ^ 59
def prefixEnd_2389490 : Nat := 4983230072969 + 3 ^ 40 * 2389490 * 2
def baseEnd_2389490 : Nat := 272657086469324742907987

theorem tailTrace_2389490 : CollatzResearch.WordTrace tailWord_2389490 prefixEnd_2389490 272657086469324742907987 := by
  unfold tailWord_2389490
  simp only [CollatzResearch.WordTrace]
  refine ⟨21787965028323324311803481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58101240075528864831475949 21787965028323324311803481)
  ·
    refine ⟨16340973771242493233852611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21787965028323324311803481 16340973771242493233852611)
    ·
      refine ⟨24511460656863739850778917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16340973771242493233852611 24511460656863739850778917)
      ·
        refine ⟨4595898873161951222021047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 24511460656863739850778917 4595898873161951222021047)
        ·
          refine ⟨6893848309742926833031571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4595898873161951222021047 6893848309742926833031571)
          ·
            refine ⟨10340772464614390249547357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6893848309742926833031571 10340772464614390249547357)
            ·
              refine ⟨3877789674230396343580259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10340772464614390249547357 3877789674230396343580259)
              ·
                refine ⟨5816684511345594515370389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3877789674230396343580259 5816684511345594515370389)
                ·
                  refine ⟨272657086469324742907987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5816684511345594515370389 272657086469324742907987)
                  ·
                    rfl

theorem cell22_2389490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 1, 6].length) (baseStart_2389490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389490 prefixEnd_2389490 := by exact prefixLift 2389490
  have htrace : WordTrace (prefixWord ++ tailWord_2389490) baseStart_2389490 baseEnd_2389490 := by
    simpa [prefixWord, tailWord_2389490, baseEnd_2389490] using wordTrace_append hprefix tailTrace_2389490
  have hstable : (prefixWord ++ tailWord_2389490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389490).length < 2 ^ (prefixWord ++ tailWord_2389490).sum := by decide
  have hdescent : baseEnd_2389490 < baseStart_2389490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2389578 : List Nat := [3, 1, 2, 1, 1, 3, 1, 2, 1, 7]
def baseStart_2389578 : Nat := 118140960795 + 2389578 * 2 ^ 59
def prefixEnd_2389578 : Nat := 4983230072969 + 3 ^ 40 * 2389578 * 2
def baseEnd_2389578 : Nat := 818001383606371332523691

theorem tailTrace_2389578 : CollatzResearch.WordTrace tailWord_2389578 prefixEnd_2389578 818001383606371332523691 := by
  unfold tailWord_2389578
  simp only [CollatzResearch.WordTrace]
  refine ⟨21788767434243622069104347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 58103379824649658850944925 21788767434243622069104347)
  ·
    refine ⟨32683151151365433103656521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21788767434243622069104347 32683151151365433103656521)
    ·
      refine ⟨24512363363524074827742391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 32683151151365433103656521 24512363363524074827742391)
      ·
        refine ⟨36768545045286112241613587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 24512363363524074827742391 36768545045286112241613587)
        ·
          refine ⟨55152817567929168362420381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 36768545045286112241613587 55152817567929168362420381)
          ·
            refine ⟨20682306587973438135907643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 55152817567929168362420381 20682306587973438135907643)
            ·
              refine ⟨31023459881960157203861465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 20682306587973438135907643 31023459881960157203861465)
              ·
                refine ⟨23267594911470117902896099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31023459881960157203861465 23267594911470117902896099)
                ·
                  refine ⟨34901392367205176854344149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23267594911470117902896099 34901392367205176854344149)
                  ·
                    refine ⟨818001383606371332523691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 34901392367205176854344149 818001383606371332523691)
                    ·
                      rfl

theorem cell22_2389578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_2389578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2389578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2389578 prefixEnd_2389578 := by exact prefixLift 2389578
  have htrace : WordTrace (prefixWord ++ tailWord_2389578) baseStart_2389578 baseEnd_2389578 := by
    simpa [prefixWord, tailWord_2389578, baseEnd_2389578] using wordTrace_append hprefix tailTrace_2389578
  have hstable : (prefixWord ++ tailWord_2389578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2389578).length < 2 ^ (prefixWord ++ tailWord_2389578).sum := by decide
  have hdescent : baseEnd_2389578 < baseStart_2389578 := by decide
  rcases family_descends (prefixWord ++ tailWord_2389578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
